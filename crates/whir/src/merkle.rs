// Credits:
// - whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).
// - Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use std::any::TypeId;

use field::BasedVectorSpace;
use field::ExtensionField;
use field::Field;
use field::PackedValue;
use field::PrimeField32;
use koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use poly::*;

use rayon::prelude::*;
use symetric::Compression;
use symetric::merkle::unpack_array;
use tracing::instrument;
use utils::log2_ceil_usize;

use crate::DenseMatrix;
use crate::Dimensions;
use crate::Matrix;
pub use symetric::DIGEST_ELEMS;

fn blake3_digest_to_field(hash_bytes: &[u8; 32]) -> [KoalaBear; DIGEST_ELEMS] {
    std::array::from_fn(|j| {
        let val = u32::from_le_bytes(hash_bytes[j * 4..j * 4 + 4].try_into().unwrap());
        KoalaBear::new(val % KoalaBear::ORDER_U32)
    })
}

fn blake3_leaf_hash(row: &[KoalaBear], full_base_width: usize) -> [KoalaBear; DIGEST_ELEMS] {
    let row_bytes: &[u8] =
        unsafe { std::slice::from_raw_parts(row.as_ptr() as *const u8, row.len() * 4) };
    let padding_bytes = (full_base_width - row.len()) * 4;
    let hash = if padding_bytes == 0 {
        blake3::hash(row_bytes)
    } else {
        let byte_len = full_base_width * 4;
        const STACK_LIMIT: usize = 4096;
        if byte_len <= STACK_LIMIT {
            let mut buf = [0u8; STACK_LIMIT];
            buf[..row_bytes.len()].copy_from_slice(row_bytes);
            blake3::hash(&buf[..byte_len])
        } else {
            let mut buf = vec![0u8; byte_len];
            buf[..row_bytes.len()].copy_from_slice(row_bytes);
            blake3::hash(&buf)
        }
    };
    blake3_digest_to_field(hash.as_bytes())
}

fn blake3_compress_internal(left: [KoalaBear; DIGEST_ELEMS], right: [KoalaBear; DIGEST_ELEMS]) -> [KoalaBear; DIGEST_ELEMS] {
    let left_bytes: &[u8; DIGEST_ELEMS * 4] = unsafe { &*(&left as *const _ as *const _) };
    let right_bytes: &[u8; DIGEST_ELEMS * 4] = unsafe { &*(&right as *const _ as *const _) };
    let mut buf = [0u8; DIGEST_ELEMS * 2 * 4];
    buf[..DIGEST_ELEMS * 4].copy_from_slice(left_bytes);
    buf[DIGEST_ELEMS * 4..].copy_from_slice(right_bytes);
    let hash = blake3::hash(&buf);
    blake3_digest_to_field(hash.as_bytes())
}

#[instrument(name = "first digest layer (blake3)", level = "debug", skip_all)]
fn first_digest_layer_blake3(
    matrix: &DenseMatrix<KoalaBear>,
    full_base_width: usize,
) -> Vec<[KoalaBear; DIGEST_ELEMS]> {
    let height = matrix.height();
    let matrix_width = matrix.width();
    let mut digests = vec![[KoalaBear::default(); DIGEST_ELEMS]; height];

    digests.par_iter_mut().enumerate().for_each(|(i, digest)| {
        let row_slice = unsafe { matrix.row_subslice_unchecked(i, 0, matrix_width) };
        *digest = blake3_leaf_hash(&row_slice, full_base_width);
    });

    digests
}

fn merkle_verify_blake3(
    commit: &[KoalaBear; DIGEST_ELEMS],
    log_height: usize,
    mut index: usize,
    opened_values: &[KoalaBear],
    opening_proof: &[[KoalaBear; DIGEST_ELEMS]],
) -> bool {
    if opening_proof.len() != log_height {
        return false;
    }
    let mut root = blake3_leaf_hash(opened_values, opened_values.len());
    for &sibling in opening_proof.iter() {
        let (left, right) = if index & 1 == 0 {
            (root, sibling)
        } else {
            (sibling, root)
        };
        root = blake3_compress_internal(left, right);
        index >>= 1;
    }
    commit == &root
}

pub(crate) type RoundMerkleTree<F> = WhirMerkleTree<F, DenseMatrix<F>, DIGEST_ELEMS>;

#[allow(clippy::missing_transmute_annotations)]
pub(crate) fn merkle_commit<F: Field, EF: ExtensionField<F>>(
    matrix: DenseMatrix<EF>,
    full_n_cols: usize,
    effective_n_cols: usize,
) -> ([F; DIGEST_ELEMS], RoundMerkleTree<F>) {
    if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, QuinticExtensionFieldKB)>() {
        let matrix = unsafe { std::mem::transmute::<_, DenseMatrix<QuinticExtensionFieldKB>>(matrix) };
        let dim = <QuinticExtensionFieldKB as BasedVectorSpace<KoalaBear>>::DIMENSION;
        let dft_base_width = matrix.width * dim;
        let full_base_width = full_n_cols * dim;
        let effective_base_width = effective_n_cols * dim;
        let base_values = QuinticExtensionFieldKB::flatten_to_base(matrix.values);
        let base_matrix = DenseMatrix::<KoalaBear>::new(base_values, dft_base_width);
        let tree = build_merkle_tree_koalabear(base_matrix, full_base_width, effective_base_width);
        let root: [_; DIGEST_ELEMS] = tree.root();
        let root = unsafe { std::mem::transmute_copy::<_, [F; DIGEST_ELEMS]>(&root) };
        let tree = unsafe { std::mem::transmute::<_, RoundMerkleTree<F>>(tree) };
        (root, tree)
    } else if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, KoalaBear)>() {
        let matrix = unsafe { std::mem::transmute::<_, DenseMatrix<KoalaBear>>(matrix) };
        let tree = build_merkle_tree_koalabear(matrix, full_n_cols, effective_n_cols);
        let root: [_; DIGEST_ELEMS] = tree.root();
        let root = unsafe { std::mem::transmute_copy::<_, [F; DIGEST_ELEMS]>(&root) };
        let tree = unsafe { std::mem::transmute::<_, RoundMerkleTree<F>>(tree) };
        (root, tree)
    } else {
        unimplemented!()
    }
}

#[instrument(name = "build merkle tree", skip_all)]
fn build_merkle_tree_koalabear(
    leaf: DenseMatrix<KoalaBear>,
    full_base_width: usize,
    _effective_base_width: usize,
) -> RoundMerkleTree<KoalaBear> {
    let first_layer = first_digest_layer_blake3(&leaf, full_base_width);
    let tree = symetric::merkle::MerkleTree::from_first_layer_with_fn(first_layer, &blake3_compress_internal);
    WhirMerkleTree {
        leaf,
        tree,
        full_leaf_base_width: full_base_width,
    }
}

#[allow(clippy::missing_transmute_annotations)]
pub(crate) fn merkle_open<F: Field, EF: ExtensionField<F>>(
    merkle_tree: &RoundMerkleTree<F>,
    index: usize,
) -> (Vec<EF>, Vec<[F; DIGEST_ELEMS]>) {
    if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, QuinticExtensionFieldKB)>() {
        let merkle_tree = unsafe { std::mem::transmute::<_, &RoundMerkleTree<KoalaBear>>(merkle_tree) };
        let (inner_leaf, proof) = merkle_tree.open(index);
        let leaf = QuinticExtensionFieldKB::reconstitute_from_base(inner_leaf);
        let leaf = unsafe { std::mem::transmute::<_, Vec<EF>>(leaf) };
        let proof = unsafe { std::mem::transmute::<_, Vec<[F; DIGEST_ELEMS]>>(proof) };
        (leaf, proof)
    } else if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, KoalaBear)>() {
        let merkle_tree = unsafe { std::mem::transmute::<_, &RoundMerkleTree<KoalaBear>>(merkle_tree) };
        let (inner_leaf, proof) = merkle_tree.open(index);
        let leaf = KoalaBear::reconstitute_from_base(inner_leaf);
        let leaf = unsafe { std::mem::transmute::<_, Vec<EF>>(leaf) };
        let proof = unsafe { std::mem::transmute::<_, Vec<[F; DIGEST_ELEMS]>>(proof) };
        (leaf, proof)
    } else {
        unimplemented!()
    }
}

#[allow(clippy::missing_transmute_annotations)]
pub(crate) fn merkle_verify<F: Field, EF: ExtensionField<F>>(
    merkle_root: [F; DIGEST_ELEMS],
    index: usize,
    dimension: Dimensions,
    data: Vec<EF>,
    proof: &Vec<[F; DIGEST_ELEMS]>,
) -> bool {
    let log_max_height = utils::log2_strict_usize(dimension.height.next_power_of_two());
    if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, QuinticExtensionFieldKB)>() {
        let merkle_root = unsafe { std::mem::transmute_copy::<_, [KoalaBear; DIGEST_ELEMS]>(&merkle_root) };
        let data = unsafe { std::mem::transmute::<_, Vec<QuinticExtensionFieldKB>>(data) };
        let proof = unsafe { std::mem::transmute::<_, &Vec<[KoalaBear; DIGEST_ELEMS]>>(proof) };
        let base_data = QuinticExtensionFieldKB::flatten_to_base(data);
        merkle_verify_blake3(&merkle_root, log_max_height, index, &base_data, proof)
    } else if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, KoalaBear)>() {
        let merkle_root = unsafe { std::mem::transmute_copy::<_, [KoalaBear; DIGEST_ELEMS]>(&merkle_root) };
        let data = unsafe { std::mem::transmute::<_, Vec<KoalaBear>>(data) };
        let proof = unsafe { std::mem::transmute::<_, &Vec<[KoalaBear; DIGEST_ELEMS]>>(proof) };
        let base_data = KoalaBear::flatten_to_base(data);
        merkle_verify_blake3(&merkle_root, log_max_height, index, &base_data, proof)
    } else {
        unimplemented!()
    }
}

#[derive(Debug, Clone)]
pub struct WhirMerkleTree<F, M, const DIGEST_ELEMS: usize> {
    pub(crate) leaf: M,
    pub(crate) tree: symetric::merkle::MerkleTree<F, DIGEST_ELEMS>,
    full_leaf_base_width: usize,
}

impl<F: Clone + Copy + Default + Send + Sync, M: Matrix<F>, const DIGEST_ELEMS: usize>
    WhirMerkleTree<F, M, DIGEST_ELEMS>
{
    #[instrument(name = "build merkle tree", skip_all)]
    pub fn new<P, Perm, const WIDTH: usize, const RATE: usize>(
        perm: &Perm,
        leaf: M,
        full_leaf_base_width: usize,
        effective_base_width: usize,
    ) -> Self
    where
        P: PackedValue<Value = F> + Default,
        Perm: Compression<[F; WIDTH]> + Compression<[P; WIDTH]>,
    {
        let n_zero_suffix_rate_chunks = (full_leaf_base_width - effective_base_width) / RATE;
        let first_layer = if n_zero_suffix_rate_chunks >= 2 {
            let scalar_state = symetric::precompute_zero_suffix_state::<F, Perm, WIDTH, RATE, DIGEST_ELEMS>(
                perm,
                n_zero_suffix_rate_chunks,
            );
            let packed_state: [P; WIDTH] = std::array::from_fn(|i| P::from_fn(|_| scalar_state[i]));
            first_digest_layer_with_initial_state::<P, Perm, _, DIGEST_ELEMS, WIDTH, RATE>(
                perm,
                &leaf,
                &packed_state,
                effective_base_width,
            )
        } else {
            first_digest_layer::<P, Perm, _, DIGEST_ELEMS, WIDTH, RATE>(perm, &leaf, full_leaf_base_width)
        };
        let tree = symetric::merkle::MerkleTree::from_first_layer::<P, Perm, WIDTH>(perm, first_layer);
        Self {
            leaf,
            tree,
            full_leaf_base_width,
        }
    }

    #[must_use]
    pub fn root(&self) -> [F; DIGEST_ELEMS] {
        self.tree.root()
    }

    pub fn open(&self, index: usize) -> (Vec<F>, Vec<[F; DIGEST_ELEMS]>) {
        let log_height = log2_ceil_usize(self.leaf.height());
        let mut opening: Vec<F> = self.leaf.row(index).unwrap().into_iter().collect();
        opening.resize(self.full_leaf_base_width, F::default());
        let proof = self.tree.open_siblings(index, log_height);
        (opening, proof)
    }
}

#[instrument(name = "first digest layer", level = "debug", skip_all)]
fn first_digest_layer<P, Perm, M, const DIGEST_ELEMS: usize, const WIDTH: usize, const RATE: usize>(
    perm: &Perm,
    matrix: &M,
    full_width: usize,
) -> Vec<[P::Value; DIGEST_ELEMS]>
where
    P: PackedValue + Default,
    P::Value: Default + Copy,
    Perm: Compression<[P::Value; WIDTH]> + Compression<[P; WIDTH]>,
    M: Matrix<P::Value>,
{
    let width = P::WIDTH;
    let height = matrix.height();
    assert!(height.is_multiple_of(width));
    let matrix_width = matrix.width();
    let n_trailing_zeros = full_width - matrix_width;

    let mut digests = unsafe { uninitialized_vec(height) };

    digests
        .par_chunks_exact_mut(width)
        .enumerate()
        .for_each(|(i, digests_chunk)| {
            let first_row = i * width;
            let rtl_iter = matrix.vertically_packed_row_rtl::<P>(first_row, matrix_width, n_trailing_zeros);
            let packed_digest: [P; DIGEST_ELEMS] =
                symetric::hash_rtl_iter::<_, _, _, WIDTH, RATE, DIGEST_ELEMS>(perm, rtl_iter);
            for (dst, src) in digests_chunk.iter_mut().zip(unpack_array(packed_digest)) {
                *dst = src;
            }
        });

    digests
}

#[instrument(skip_all)]
fn first_digest_layer_with_initial_state<P, Perm, M, const DIGEST_ELEMS: usize, const WIDTH: usize, const RATE: usize>(
    perm: &Perm,
    matrix: &M,
    packed_initial_state: &[P; WIDTH],
    effective_base_width: usize,
) -> Vec<[P::Value; DIGEST_ELEMS]>
where
    P: PackedValue + Default,
    P::Value: Default + Copy,
    Perm: Compression<[P::Value; WIDTH]> + Compression<[P; WIDTH]>,
    M: Matrix<P::Value>,
{
    let width = P::WIDTH;
    let height = matrix.height();
    assert!(height.is_multiple_of(width));
    let n_pad = (RATE - effective_base_width % RATE) % RATE;

    let mut digests = unsafe { uninitialized_vec(height) };

    digests
        .par_chunks_exact_mut(width)
        .enumerate()
        .for_each(|(i, digests_chunk)| {
            let first_row = i * width;
            let rtl_iter = matrix.vertically_packed_row_rtl::<P>(first_row, effective_base_width, n_pad);
            let packed_digest: [P; DIGEST_ELEMS] =
                symetric::hash_rtl_iter_with_initial_state::<_, _, _, WIDTH, RATE, DIGEST_ELEMS>(
                    perm,
                    rtl_iter,
                    packed_initial_state,
                );
            for (dst, src) in digests_chunk.iter_mut().zip(unpack_array(packed_digest)) {
                *dst = src;
            }
        });

    digests
}
