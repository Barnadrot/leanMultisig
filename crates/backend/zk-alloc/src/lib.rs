//! Bump-pointer arena allocator.
//!
//! One mmap region split into per-thread slabs. Allocation = increment a thread-local
//! pointer; free = no-op. `begin_phase()` resets the arena: each thread's next
//! allocation starts over at the beginning of its slab, overwriting the previous
//! phase's data. Allocations that don't fit (too large, or beyond `MAX_THREADS`) fall
//! back to the system allocator.
//!
//! ```ignore
//! init();                          // once, at process start
//! loop {
//!     begin_phase();               // arena ON; slabs reset lazily
//!     let res = heavy_work();      // fast increments
//!     end_phase();                 // arena OFF; new allocations go to System
//!     let copy = res.clone();      // detach from arena before next phase resets it
//! }
//! ```

use std::alloc::{GlobalAlloc, Layout};
use std::cell::Cell;
use std::sync::Once;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use system_info::NUM_THREADS;

mod syscall;

const HOT_SLAB_SIZE: usize = 1 << 30; // 1GB hugetlb-backed per slab
const COLD_SLAB_SIZE: usize = 7 << 30; // 7GB regular pages per slab
const SLACK: usize = 4;
const MAX_THREADS: usize = NUM_THREADS + SLACK;
const HOT_REGION_SIZE: usize = HOT_SLAB_SIZE * MAX_THREADS;
const COLD_REGION_SIZE: usize = COLD_SLAB_SIZE * MAX_THREADS;

#[derive(Debug)]
pub struct ZkAllocator;

/// Incremented by `begin_phase()`. Every thread caches the last value it saw in
/// `ARENA_GEN`; when they differ, the thread resets its allocation cursor to the start
/// of its slab on the next allocation. This is how a single store on the main thread
/// "resets" every other thread's slab without any cross-thread synchronization.
static GENERATION: AtomicUsize = AtomicUsize::new(0);

/// Master switch for the arena. `true` (set by `begin_phase`) routes allocations
/// through the arena; `false` (set by `end_phase`) routes them to the system allocator.
static ARENA_ACTIVE: AtomicBool = AtomicBool::new(false);

/// Base address of the hot (hugetlb) mmap'd region, or `0` before `ensure_region` runs.
static HOT_REGION_BASE: AtomicUsize = AtomicUsize::new(0);

/// Base address of the cold (regular pages) mmap'd region, or `0` before init.
static COLD_REGION_BASE: AtomicUsize = AtomicUsize::new(0);

/// Synchronizes the one-time mmap so concurrent first-allocators don't race.
static REGION_INIT: Once = Once::new();

/// Monotonic counter handed out to threads to pick their slab. `fetch_add`'d once per
/// thread on its first arena allocation. Threads that get `idx >= MAX_THREADS` mark
/// themselves `ARENA_NO_SLAB` and permanently fall through to the system allocator.
static THREAD_IDX: AtomicUsize = AtomicUsize::new(0);

thread_local! {
    /// Where this thread's next allocation lands.
    static ARENA_PTR: Cell<usize> = const { Cell::new(0) };
    /// One past the last byte of the current active region (hot or cold).
    static ARENA_END: Cell<usize> = const { Cell::new(0) };
    /// Base of this thread's hot slab (hugetlb). Also the phase-reset target.
    static ARENA_BASE: Cell<usize> = const { Cell::new(0) };
    /// One past the last byte of the hot slab. Used to detect hot→cold overflow.
    static ARENA_HOT_END: Cell<usize> = const { Cell::new(0) };
    /// Base of this thread's cold slab (regular pages).
    static ARENA_COLD_BASE: Cell<usize> = const { Cell::new(0) };
    /// One past the last byte of the cold slab.
    static ARENA_COLD_END: Cell<usize> = const { Cell::new(0) };
    /// Last generation value this thread observed.
    static ARENA_GEN: Cell<usize> = const { Cell::new(0) };
    /// `true` after this thread overflowed from hot to cold in this phase.
    static ARENA_IN_COLD: Cell<bool> = const { Cell::new(false) };
    /// `true` if this thread exhausted MAX_THREADS.
    static ARENA_NO_SLAB: Cell<bool> = const { Cell::new(false) };
}

/// Ensures both hot (hugetlb) and cold (regular) regions are mapped. Returns the
/// hot region base address.
fn ensure_region() -> usize {
    REGION_INIT.call_once(|| {
        let hot = unsafe { syscall::mmap_hugetlb(HOT_REGION_SIZE) };
        if hot.is_null() {
            std::process::abort();
        }
        HOT_REGION_BASE.store(hot as usize, Ordering::Release);

        let cold = unsafe { syscall::mmap_anonymous(COLD_REGION_SIZE) };
        if cold.is_null() {
            std::process::abort();
        }
        unsafe { syscall::madvise(cold, COLD_REGION_SIZE, syscall::MADV_NOHUGEPAGE) };
        COLD_REGION_BASE.store(cold as usize, Ordering::Release);
    });
    HOT_REGION_BASE.load(Ordering::Acquire)
}

/// Call once at process start, before any `begin_phase()`.
pub fn init() {
    let actual_num_threads = std::thread::available_parallelism().unwrap().get();
    assert_eq!(
        actual_num_threads, NUM_THREADS,
        "built for {NUM_THREADS} threads but this machine reports {actual_num_threads} -> please rebuild`"
    );
}

/// Activates the arena and resets every thread's slab. All allocations until the next
/// `end_phase()` go to the arena; the previous phase's data is overwritten in place.
pub fn begin_phase() {
    GENERATION.fetch_add(1, Ordering::Release);
    ARENA_ACTIVE.store(true, Ordering::Release);
}

/// Deactivates the arena. New allocations go to the system allocator; existing arena
/// pointers stay valid until the next `begin_phase()` resets the slabs.
///
/// Also calls [`system_info::flush_rayon`] to release any rayon/crossbeam storage
/// still referencing this phase's arena memory.
pub fn end_phase() {
    ARENA_ACTIVE.store(false, Ordering::Release);
    system_info::flush_rayon();
}

#[cold]
#[inline(never)]
unsafe fn arena_alloc_cold(size: usize, align: usize) -> *mut u8 {
    let generation = GENERATION.load(Ordering::Relaxed);
    if !ARENA_NO_SLAB.get() {
        if ARENA_GEN.get() != generation {
            // Generation mismatch — reset to start of hot slab.
            let mut base = ARENA_BASE.get();
            if base == 0 {
                let hot_region = ensure_region();
                let cold_region = COLD_REGION_BASE.load(Ordering::Acquire);
                let idx = THREAD_IDX.fetch_add(1, Ordering::Relaxed);
                if idx >= MAX_THREADS {
                    ARENA_NO_SLAB.set(true);
                    return unsafe { std::alloc::System.alloc(Layout::from_size_align_unchecked(size, align)) };
                }
                base = hot_region + idx * HOT_SLAB_SIZE;
                ARENA_BASE.set(base);
                ARENA_HOT_END.set(base + HOT_SLAB_SIZE);
                let cold_base = cold_region + idx * COLD_SLAB_SIZE;
                ARENA_COLD_BASE.set(cold_base);
                ARENA_COLD_END.set(cold_base + COLD_SLAB_SIZE);
            }
            ARENA_PTR.set(base);
            ARENA_END.set(ARENA_HOT_END.get());
            ARENA_IN_COLD.set(false);
            ARENA_GEN.set(generation);
            let aligned = base.next_multiple_of(align);
            let new_ptr = aligned + size;
            if new_ptr <= ARENA_END.get() {
                ARENA_PTR.set(new_ptr);
                return aligned as *mut u8;
            }
        }
        // Hot slab exhausted — switch to cold slab (once per phase).
        if !ARENA_IN_COLD.get() {
            ARENA_IN_COLD.set(true);
            let cold_base = ARENA_COLD_BASE.get();
            let cold_end = ARENA_COLD_END.get();
            if cold_base != 0 {
                let aligned = cold_base.next_multiple_of(align);
                let new_ptr = aligned + size;
                if new_ptr <= cold_end {
                    ARENA_PTR.set(new_ptr);
                    ARENA_END.set(cold_end);
                    return aligned as *mut u8;
                }
            }
        }
    }
    unsafe { std::alloc::System.alloc(Layout::from_size_align_unchecked(size, align)) }
}

// SAFETY: All pointers returned are either from our mmap'd region (valid, aligned,
// non-overlapping per thread) or from System. The arena is thread-local so no data
// races. Relaxed ordering on ARENA_ACTIVE/GENERATION is sound: worst case a thread
// sees a stale value and does one extra system-alloc before picking up the new
// generation on the next call.
unsafe impl GlobalAlloc for ZkAllocator {
    #[inline(always)]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if ARENA_ACTIVE.load(Ordering::Relaxed) {
            let generation = GENERATION.load(Ordering::Relaxed);
            if ARENA_GEN.get() == generation {
                let align = layout.align();
                let aligned = (ARENA_PTR.get() + align - 1) & !(align - 1);
                let new_ptr = aligned + layout.size();
                if new_ptr <= ARENA_END.get() {
                    ARENA_PTR.set(new_ptr);
                    return aligned as *mut u8;
                }
            }
            return unsafe { arena_alloc_cold(layout.size(), layout.align()) };
        }
        unsafe { std::alloc::System.alloc(layout) }
    }

    #[inline(always)]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        let addr = ptr as usize;
        let hot = HOT_REGION_BASE.load(Ordering::Relaxed);
        if hot != 0 && addr >= hot && addr < hot + HOT_REGION_SIZE {
            return;
        }
        let cold = COLD_REGION_BASE.load(Ordering::Relaxed);
        if cold != 0 && addr >= cold && addr < cold + COLD_REGION_SIZE {
            return;
        }
        unsafe { std::alloc::System.dealloc(ptr, layout) };
    }

    #[inline(always)]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        if new_size <= layout.size() {
            return ptr;
        }
        // SAFETY: new_size > layout.size() > 0, align unchanged from valid layout.
        let new_layout = unsafe { Layout::from_size_align_unchecked(new_size, layout.align()) };
        let new_ptr = unsafe { self.alloc(new_layout) };
        if !new_ptr.is_null() {
            unsafe { std::ptr::copy_nonoverlapping(ptr, new_ptr, layout.size()) };
            unsafe { self.dealloc(ptr, layout) };
        }
        new_ptr
    }
}
