// Credits:
// - Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use std::array;

use field::PackedValue;
use rayon::prelude::*;

use crate::Compression;

pub const DIGEST_ELEMS: usize = 8;

/// A Merkle tree storing only the digest layers (no leaf data).
#[derive(Debug, Clone)]
pub struct MerkleTree<F, const DIGEST_ELEMS: usize> {
    pub digest_layers: Vec<Vec<[F; DIGEST_ELEMS]>>,
}

impl<F: Clone + Copy + Default + Send + Sync, const DIGEST_ELEMS: usize> MerkleTree<F, DIGEST_ELEMS> {
    /// Build a Merkle tree from a pre-computed first digest layer.
    pub fn from_first_layer<P, Comp, const WIDTH: usize>(comp: &Comp, first_layer: Vec<[F; DIGEST_ELEMS]>) -> Self
    where
        P: PackedValue<Value = F> + Default,
        Comp: Compression<[F; WIDTH]> + Compression<[P; WIDTH]>,
    {
        let mut digest_layers = vec![first_layer];
        loop {
            let prev_layer = digest_layers.last().unwrap().as_slice();
            if prev_layer.len() == 1 {
                break;
            }
            digest_layers.push(compress_layer::<P, Comp, DIGEST_ELEMS, WIDTH>(prev_layer, comp));
        }
        Self { digest_layers }
    }

    #[must_use]
    pub fn root(&self) -> [F; DIGEST_ELEMS] {
        self.digest_layers.last().unwrap()[0]
    }

    /// Returns the sibling digests along the path from leaf to root.
    pub fn open_siblings(&self, index: usize, log_height: usize) -> Vec<[F; DIGEST_ELEMS]> {
        (0..log_height)
            .map(|i| self.digest_layers[i][(index >> i) ^ 1])
            .collect()
    }
}

pub fn compress_layer<P, Comp, const DIGEST_ELEMS: usize, const WIDTH: usize>(
    prev_layer: &[[P::Value; DIGEST_ELEMS]],
    comp: &Comp,
) -> Vec<[P::Value; DIGEST_ELEMS]>
where
    P: PackedValue + Default,
    P::Value: Default + Copy,
    Comp: Compression<[P::Value; WIDTH]> + Compression<[P; WIDTH]>,
{
    let width = P::WIDTH;
    let stride = 2 * width;
    let next_len_padded = if prev_layer.len() == 2 {
        1
    } else {
        (prev_layer.len() / 2 + 1) & !1
    };
    let next_len = prev_layer.len() / 2;

    let default_digest = [P::Value::default(); DIGEST_ELEMS];
    let mut next_digests = vec![default_digest; next_len_padded];

    // x2-batched packed path: each closure invocation processes 2*width
    // leaf-pairs via one compress_x2 call, exposing cross-permutation ILP.
    let n_x2 = next_len / stride;
    next_digests[0..n_x2 * stride]
        .par_chunks_exact_mut(stride)
        .enumerate()
        .for_each(|(i, digests_chunk)| {
            let first_row_a = i * stride;
            let first_row_b = first_row_a + width;
            let left_a = array::from_fn(|j| P::from_fn(|k| prev_layer[2 * (first_row_a + k)][j]));
            let right_a =
                array::from_fn(|j| P::from_fn(|k| prev_layer[2 * (first_row_a + k) + 1][j]));
            let left_b = array::from_fn(|j| P::from_fn(|k| prev_layer[2 * (first_row_b + k)][j]));
            let right_b =
                array::from_fn(|j| P::from_fn(|k| prev_layer[2 * (first_row_b + k) + 1][j]));
            let [packed_a, packed_b] = crate::compress_x2(comp, [left_a, right_a], [left_b, right_b]);
            let (dst_a, dst_b) = digests_chunk.split_at_mut(width);
            for (dst, src) in dst_a.iter_mut().zip(unpack_array(packed_a)) {
                *dst = src;
            }
            for (dst, src) in dst_b.iter_mut().zip(unpack_array(packed_b)) {
                *dst = src;
            }
        });

    // Single packed batch for the remaining [n_x2*stride, next_len/width*width) range
    // (at most one width-sized chunk left since stride = 2*width).
    let x1_start = n_x2 * stride;
    let x1_end = next_len / width * width;
    if x1_end > x1_start {
        debug_assert_eq!(x1_end - x1_start, width);
        let first_row = x1_start;
        let left = array::from_fn(|j| P::from_fn(|k| prev_layer[2 * (first_row + k)][j]));
        let right = array::from_fn(|j| P::from_fn(|k| prev_layer[2 * (first_row + k) + 1][j]));
        let packed_digest = crate::compress(comp, [left, right]);
        for (dst, src) in next_digests[first_row..first_row + width]
            .iter_mut()
            .zip(unpack_array(packed_digest))
        {
            *dst = src;
        }
    }

    // Scalar tail for [next_len/width*width, next_len).
    for i in (next_len / width * width)..next_len {
        let left = prev_layer[2 * i];
        let right = prev_layer[2 * i + 1];
        next_digests[i] = crate::compress(comp, [left, right]);
    }

    next_digests
}

pub fn merkle_verify<F, Comp, const DIGEST_ELEMS: usize, const WIDTH: usize, const RATE: usize>(
    comp: &Comp,
    commit: &[F; DIGEST_ELEMS],
    log_height: usize,
    mut index: usize,
    opened_values: &[F],
    opening_proof: &[[F; DIGEST_ELEMS]],
) -> bool
where
    F: Default + Copy + PartialEq,
    Comp: Compression<[F; WIDTH]>,
{
    if opening_proof.len() != log_height {
        return false;
    }

    let mut root = crate::hash_slice::<_, _, WIDTH, RATE, DIGEST_ELEMS>(comp, opened_values);

    for &sibling in opening_proof.iter() {
        let (left, right) = if index & 1 == 0 {
            (root, sibling)
        } else {
            (sibling, root)
        };
        root = crate::compress(comp, [left, right]);
        index >>= 1;
    }

    commit == &root
}

#[inline]
pub fn unpack_array<P: PackedValue, const N: usize>(packed_digest: [P; N]) -> impl Iterator<Item = [P::Value; N]> {
    (0..P::WIDTH).map(move |j| packed_digest.map(|p| p.as_slice()[j]))
}
