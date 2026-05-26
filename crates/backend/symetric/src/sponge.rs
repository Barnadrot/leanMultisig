// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use crate::Compression;
use field::PrimeCharacteristicRing;

/// Absorbs `data` RTL into an IV state `[data.len(), 0, ..., 0]` in RATE-sized chunks.
/// assumes data length is a multiple of RATE (= 8 in practice).
pub fn hash_slice<T, Comp, const WIDTH: usize, const RATE: usize, const OUT: usize>(comp: &Comp, data: &[T]) -> [T; OUT]
where
    T: PrimeCharacteristicRing,
    Comp: Compression<[T; WIDTH]>,
{
    debug_assert!(RATE == OUT);
    debug_assert!(WIDTH == OUT + RATE);
    debug_assert!(data.len().is_multiple_of(RATE));
    let mut state = [T::default(); WIDTH];
    state[0] = T::from_usize(data.len());
    for chunk in data.chunks_exact(RATE).rev() {
        state[WIDTH - RATE..].copy_from_slice(chunk);
        comp.compress_mut(&mut state);
    }
    state[..OUT].try_into().unwrap()
}

/// Precompute sponge state after absorbing `n_zero_chunks` all-zero RATE-chunks
/// into an IV state `[iv_first, 0, ..., 0]`. Caller provides `iv_first` (typically
/// the length, in field elements, of the full slice that will eventually be hashed).
pub fn precompute_zero_suffix_state<T, Comp, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    comp: &Comp,
    iv_first: T,
    n_zero_chunks: usize,
) -> [T; WIDTH]
where
    T: PrimeCharacteristicRing,
    Comp: Compression<[T; WIDTH]>,
{
    debug_assert!(RATE == OUT);
    debug_assert!(WIDTH == OUT + RATE);
    let mut state = [T::default(); WIDTH];
    state[0] = iv_first;
    for _ in 0..n_zero_chunks {
        for s in &mut state[WIDTH - RATE..] {
            *s = T::default();
        }
        comp.compress_mut(&mut state);
    }
    state
}

/// RTL = Right-to-left. Absorbs starting from the provided `initial_state` in RATE-sized chunks.
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
    debug_assert!(RATE == OUT);
    debug_assert!(WIDTH == OUT + RATE);
    let mut state = *initial_state;
    while let Some(elem) = iter.next() {
        state[WIDTH - 1] = elem;
        for pos in (WIDTH - RATE..WIDTH - 1).rev() {
            state[pos] = iter.next().unwrap();
        }
        comp.compress_mut(&mut state);
    }
    state[..OUT].try_into().unwrap()
}

/// Interleaved 2x RTL sponge: processes two independent sponge chains in lockstep,
/// alternating compress_mut calls to hide Poseidon pipeline latency.
#[inline(always)]
pub fn hash_rtl_iter_interleaved_2x<T, Comp, I0, I1, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    comp: &Comp,
    mut iter_a: I0,
    mut iter_b: I1,
    initial_state: &[T; WIDTH],
) -> ([T; OUT], [T; OUT])
where
    T: Default + Copy,
    Comp: Compression<[T; WIDTH]>,
    I0: Iterator<Item = T>,
    I1: Iterator<Item = T>,
{
    debug_assert!(RATE == OUT);
    debug_assert!(WIDTH == OUT + RATE);
    let mut state_a = *initial_state;
    let mut state_b = *initial_state;
    loop {
        let elem_a = iter_a.next();
        let elem_b = iter_b.next();
        match (elem_a, elem_b) {
            (Some(ea), Some(eb)) => {
                state_a[WIDTH - 1] = ea;
                state_b[WIDTH - 1] = eb;
                for pos in (WIDTH - RATE..WIDTH - 1).rev() {
                    state_a[pos] = iter_a.next().unwrap();
                    state_b[pos] = iter_b.next().unwrap();
                }
                comp.compress_mut(&mut state_a);
                comp.compress_mut(&mut state_b);
            }
            (Some(ea), None) => {
                state_a[WIDTH - 1] = ea;
                for pos in (WIDTH - RATE..WIDTH - 1).rev() {
                    state_a[pos] = iter_a.next().unwrap();
                }
                comp.compress_mut(&mut state_a);
                while let Some(e) = iter_a.next() {
                    state_a[WIDTH - 1] = e;
                    for pos in (WIDTH - RATE..WIDTH - 1).rev() {
                        state_a[pos] = iter_a.next().unwrap();
                    }
                    comp.compress_mut(&mut state_a);
                }
            }
            _ => break,
        }
    }
    (
        state_a[..OUT].try_into().unwrap(),
        state_b[..OUT].try_into().unwrap(),
    )
}

/// Trait for permutations that support interleaved 2x compression.
pub trait Compress2x<T> {
    fn compress_2x(&self, a: &mut T, b: &mut T);
}

/// Interleaved 2x RTL sponge using round-level interleaving via Compress2x.
#[inline(always)]
pub fn hash_rtl_iter_interleaved_2x_deep<T, Comp, I0, I1, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    comp: &Comp,
    mut iter_a: I0,
    mut iter_b: I1,
    initial_state: &[T; WIDTH],
) -> ([T; OUT], [T; OUT])
where
    T: Default + Copy,
    Comp: Compress2x<[T; WIDTH]>,
    I0: Iterator<Item = T>,
    I1: Iterator<Item = T>,
{
    debug_assert!(RATE == OUT);
    debug_assert!(WIDTH == OUT + RATE);
    let mut state_a = *initial_state;
    let mut state_b = *initial_state;
    loop {
        let elem_a = iter_a.next();
        let elem_b = iter_b.next();
        match (elem_a, elem_b) {
            (Some(ea), Some(eb)) => {
                state_a[WIDTH - 1] = ea;
                state_b[WIDTH - 1] = eb;
                for pos in (WIDTH - RATE..WIDTH - 1).rev() {
                    state_a[pos] = iter_a.next().unwrap();
                    state_b[pos] = iter_b.next().unwrap();
                }
                comp.compress_2x(&mut state_a, &mut state_b);
            }
            (Some(ea), None) => {
                state_a[WIDTH - 1] = ea;
                for pos in (WIDTH - RATE..WIDTH - 1).rev() {
                    state_a[pos] = iter_a.next().unwrap();
                }
                let mut dummy = state_b;
                comp.compress_2x(&mut state_a, &mut dummy);
                while let Some(e) = iter_a.next() {
                    state_a[WIDTH - 1] = e;
                    for pos in (WIDTH - RATE..WIDTH - 1).rev() {
                        state_a[pos] = iter_a.next().unwrap();
                    }
                    comp.compress_2x(&mut state_a, &mut dummy);
                }
            }
            _ => break,
        }
    }
    (
        state_a[..OUT].try_into().unwrap(),
        state_b[..OUT].try_into().unwrap(),
    )
}
