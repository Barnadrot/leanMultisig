use std::sync::atomic::{AtomicUsize, Ordering};

static PHASE_FN: AtomicUsize = AtomicUsize::new(0);
static DEACT_FN: AtomicUsize = AtomicUsize::new(0);
const RESOLVED_NULL: usize = 1;

unsafe fn resolve(name: &[u8]) -> usize {
    let handle = unsafe { libc_dlsym(name) };
    if handle == 0 { RESOLVED_NULL } else { handle }
}

unsafe fn libc_dlsym(name: &[u8]) -> usize {
    unsafe extern "C" {
        fn dlsym(handle: *mut u8, symbol: *const u8) -> *mut u8;
    }
    const RTLD_DEFAULT: *mut u8 = 0 as *mut u8;
    unsafe { dlsym(RTLD_DEFAULT, name.as_ptr()) as usize }
}

pub unsafe fn phase_boundary() {
    let mut addr = PHASE_FN.load(Ordering::Relaxed);
    if addr == 0 {
        addr = unsafe { resolve(b"zk_alloc_phase_boundary\0") };
        PHASE_FN.store(addr, Ordering::Relaxed);
    }
    if addr != RESOLVED_NULL {
        let f: extern "C" fn() = unsafe { std::mem::transmute(addr) };
        f();
    }
}

pub unsafe fn deactivate() {
    let mut addr = DEACT_FN.load(Ordering::Relaxed);
    if addr == 0 {
        addr = unsafe { resolve(b"zk_alloc_deactivate\0") };
        DEACT_FN.store(addr, Ordering::Relaxed);
    }
    if addr != RESOLVED_NULL {
        let f: extern "C" fn() = unsafe { std::mem::transmute(addr) };
        f();
    }
}
