// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use crate::Compression;

pub fn compress<T: Copy + Default, Comp: Compression<[T; WIDTH]>, const CHUNK: usize, const WIDTH: usize>(
    comp: &Comp,
    input: [[T; CHUNK]; 2],
) -> [T; CHUNK] {
    debug_assert!(CHUNK * 2 <= WIDTH);
    let mut state = [T::default(); WIDTH];
    state[..CHUNK].copy_from_slice(&input[0]);
    state[CHUNK..2 * CHUNK].copy_from_slice(&input[1]);
    let out = comp.compress(state);
    out[..CHUNK].try_into().unwrap()
}

/// x2 batched compression: two independent (left, right) pairs compressed together.
/// The implementor's `compress_x2_mut` may interleave for cross-permutation ILP.
///
/// NOTE: deliberately NOT `#[inline(always)]`. The x2 body (= 2× permute body)
/// is large; inlining it into every closure caller (e.g. `compress_layer`)
/// inflates those bodies past LLVM's cost heuristic, which then outlines the
/// caller and breaks downstream inlining into the outer hot loop. Keeping
/// `compress_x2` as a single outlined function preserves caller-side inlining.
pub fn compress_x2<T: Copy + Default, Comp: Compression<[T; WIDTH]>, const CHUNK: usize, const WIDTH: usize>(
    comp: &Comp,
    input_a: [[T; CHUNK]; 2],
    input_b: [[T; CHUNK]; 2],
) -> [[T; CHUNK]; 2] {
    debug_assert!(CHUNK * 2 <= WIDTH);
    let mut state_a = [T::default(); WIDTH];
    state_a[..CHUNK].copy_from_slice(&input_a[0]);
    state_a[CHUNK..2 * CHUNK].copy_from_slice(&input_a[1]);
    let mut state_b = [T::default(); WIDTH];
    state_b[..CHUNK].copy_from_slice(&input_b[0]);
    state_b[CHUNK..2 * CHUNK].copy_from_slice(&input_b[1]);
    comp.compress_x2_mut(&mut state_a, &mut state_b);
    let out_a: [T; CHUNK] = state_a[..CHUNK].try_into().unwrap();
    let out_b: [T; CHUNK] = state_b[..CHUNK].try_into().unwrap();
    [out_a, out_b]
}
