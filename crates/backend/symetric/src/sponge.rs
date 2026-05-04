// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use crate::Compression;
use koala_bear::symmetric::Permutation;

// IV should have been added to data when necessary (typically: when the length of the data beeing hashed is not constant). Maybe we should re-add IV all the time for simplicity?
// assumes data length is a multiple of RATE (= 8 in practice).
pub fn hash_slice<T, Comp, const WIDTH: usize, const RATE: usize, const OUT: usize>(comp: &Comp, data: &[T]) -> [T; OUT]
where
    T: Default + Copy,
    Comp: Compression<[T; WIDTH]>,
{
    debug_assert!(RATE == OUT);
    debug_assert!(WIDTH == OUT + RATE);
    debug_assert!(data.len().is_multiple_of(RATE));
    let n_chunks = data.len() / RATE;
    debug_assert!(n_chunks >= 2);
    let mut state: [T; WIDTH] = data[data.len() - WIDTH..].try_into().unwrap();
    comp.compress_mut(&mut state);
    for chunk_idx in (0..n_chunks - 2).rev() {
        let offset = chunk_idx * RATE;
        state[WIDTH - RATE..].copy_from_slice(&data[offset..offset + RATE]);
        comp.compress_mut(&mut state);
    }
    state[..OUT].try_into().unwrap()
}

/// Precompute sponge state after absorbing `n_zero_chunks` all-zero RATE-chunks.
pub fn precompute_zero_suffix_state<T, Comp, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    comp: &Comp,
    n_zero_chunks: usize,
) -> [T; WIDTH]
where
    T: Default + Copy,
    Comp: Compression<[T; WIDTH]>,
{
    debug_assert!(RATE == OUT);
    debug_assert!(WIDTH == OUT + RATE);
    debug_assert!(n_zero_chunks >= 2);
    let mut state = [T::default(); WIDTH];
    comp.compress_mut(&mut state);
    for _ in 0..n_zero_chunks - 2 {
        for s in &mut state[WIDTH - RATE..] {
            *s = T::default();
        }
        comp.compress_mut(&mut state);
    }
    state
}

/// RTL = Right-to-left
#[inline(always)]
pub fn hash_rtl_iter<T, Comp, I, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    comp: &Comp,
    rtl_iter: I,
) -> [T; OUT]
where
    T: Default + Copy,
    Comp: Compression<[T; WIDTH]>,
    I: IntoIterator<Item = T>,
{
    debug_assert!(RATE == OUT);
    debug_assert!(WIDTH == OUT + RATE);
    let mut state = [T::default(); WIDTH];
    let mut iter = rtl_iter.into_iter();
    for pos in (0..WIDTH).rev() {
        state[pos] = iter.next().unwrap();
    }
    comp.compress_mut(&mut state);
    absorb_rtl_chunks::<T, Comp, _, WIDTH, RATE, OUT>(comp, &mut state, &mut iter)
}

/// RTL = Right-to-left
#[inline(always)]
pub fn hash_rtl_iter_with_initial_state<T, Comp, I, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    comp: &Comp,
    mut iter: I,
    initial_state: &[T; WIDTH],
) -> [T; OUT]
where
    T: Default + Copy,
    Comp: Compression<[T; WIDTH]>,
    I: Iterator<Item = T>,
{
    let mut state = *initial_state;
    absorb_rtl_chunks::<T, Comp, _, WIDTH, RATE, OUT>(comp, &mut state, &mut iter)
}

/// RTL = Right-to-left
#[inline(always)]
fn absorb_rtl_chunks<T, Comp, I, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    comp: &Comp,
    state: &mut [T; WIDTH],
    iter: &mut I,
) -> [T; OUT]
where
    T: Default + Copy,
    Comp: Compression<[T; WIDTH]>,
    I: Iterator<Item = T>,
{
    while let Some(elem) = iter.next() {
        state[WIDTH - 1] = elem;
        for pos in (WIDTH - RATE..WIDTH - 1).rev() {
            state[pos] = iter.next().unwrap();
        }
        comp.compress_mut(state);
    }
    state[..OUT].try_into().unwrap()
}

// --- Bare-permutation sponge variants (no Davies-Meyer feedforward) ---
// Uses `Permutation::permute_mut` directly, halving register pressure in the
// AVX-512 Poseidon fast path by eliminating the 16-register state backup.

pub fn hash_slice_perm<T, Perm, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    perm: &Perm,
    data: &[T],
) -> [T; OUT]
where
    T: Default + Copy,
    Perm: Permutation<[T; WIDTH]>,
{
    debug_assert!(RATE == OUT);
    debug_assert!(WIDTH == OUT + RATE);
    debug_assert!(data.len().is_multiple_of(RATE));
    let n_chunks = data.len() / RATE;
    debug_assert!(n_chunks >= 2);
    let mut state: [T; WIDTH] = data[data.len() - WIDTH..].try_into().unwrap();
    perm.permute_mut(&mut state);
    for chunk_idx in (0..n_chunks - 2).rev() {
        let offset = chunk_idx * RATE;
        state[WIDTH - RATE..].copy_from_slice(&data[offset..offset + RATE]);
        perm.permute_mut(&mut state);
    }
    state[..OUT].try_into().unwrap()
}

pub fn precompute_zero_suffix_state_perm<T, Perm, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    perm: &Perm,
    n_zero_chunks: usize,
) -> [T; WIDTH]
where
    T: Default + Copy,
    Perm: Permutation<[T; WIDTH]>,
{
    debug_assert!(RATE == OUT);
    debug_assert!(WIDTH == OUT + RATE);
    debug_assert!(n_zero_chunks >= 2);
    let mut state = [T::default(); WIDTH];
    perm.permute_mut(&mut state);
    for _ in 0..n_zero_chunks - 2 {
        for s in &mut state[WIDTH - RATE..] {
            *s = T::default();
        }
        perm.permute_mut(&mut state);
    }
    state
}

#[inline(always)]
pub fn hash_rtl_iter_perm<T, Perm, I, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    perm: &Perm,
    rtl_iter: I,
) -> [T; OUT]
where
    T: Default + Copy,
    Perm: Permutation<[T; WIDTH]>,
    I: IntoIterator<Item = T>,
{
    debug_assert!(RATE == OUT);
    debug_assert!(WIDTH == OUT + RATE);
    let mut state = [T::default(); WIDTH];
    let mut iter = rtl_iter.into_iter();
    for pos in (0..WIDTH).rev() {
        state[pos] = iter.next().unwrap();
    }
    perm.permute_mut(&mut state);
    absorb_rtl_chunks_perm::<T, Perm, _, WIDTH, RATE, OUT>(perm, &mut state, &mut iter)
}

#[inline(always)]
pub fn hash_rtl_iter_with_initial_state_perm<T, Perm, I, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    perm: &Perm,
    mut iter: I,
    initial_state: &[T; WIDTH],
) -> [T; OUT]
where
    T: Default + Copy,
    Perm: Permutation<[T; WIDTH]>,
    I: Iterator<Item = T>,
{
    let mut state = *initial_state;
    absorb_rtl_chunks_perm::<T, Perm, _, WIDTH, RATE, OUT>(perm, &mut state, &mut iter)
}

#[inline(always)]
fn absorb_rtl_chunks_perm<T, Perm, I, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    perm: &Perm,
    state: &mut [T; WIDTH],
    iter: &mut I,
) -> [T; OUT]
where
    T: Default + Copy,
    Perm: Permutation<[T; WIDTH]>,
    I: Iterator<Item = T>,
{
    while let Some(elem) = iter.next() {
        state[WIDTH - 1] = elem;
        for pos in (WIDTH - RATE..WIDTH - 1).rev() {
            state[pos] = iter.next().unwrap();
        }
        perm.permute_mut(state);
    }
    state[..OUT].try_into().unwrap()
}
