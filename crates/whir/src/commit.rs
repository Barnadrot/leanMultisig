// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

use fiat_shamir::FSProver;
use field::{ExtensionField, TwoAdicField};
use poly::*;
use tracing::{info_span, instrument};

use crate::*;

#[derive(Debug, Clone)]
pub enum MerkleData<EF: ExtensionField<PF<EF>>> {
    Base(RoundMerkleTree<PF<EF>>),
    Extension(RoundMerkleTree<PF<EF>>),
}

impl<EF: ExtensionField<PF<EF>>> MerkleData<EF> {
    pub(crate) fn build(
        matrix: DftOutput<EF>,
        full_n_cols: usize,
        effective_n_cols: usize,
    ) -> (Self, [PF<EF>; DIGEST_ELEMS]) {
        match matrix {
            DftOutput::Base(m) => {
                let (root, prover_data) = merkle_commit::<PF<EF>, PF<EF>>(m, full_n_cols, effective_n_cols);
                (MerkleData::Base(prover_data), root)
            }
            DftOutput::Extension(m) => {
                let (root, prover_data) = merkle_commit::<PF<EF>, EF>(m, full_n_cols, effective_n_cols);
                (MerkleData::Extension(prover_data), root)
            }
        }
    }

    pub(crate) fn open(&self, index: usize) -> (MleOwned<EF>, Vec<[PF<EF>; DIGEST_ELEMS]>) {
        match self {
            MerkleData::Base(prover_data) => {
                let (leaf, proof) = merkle_open::<PF<EF>, PF<EF>>(prover_data, index);
                (MleOwned::Base(leaf), proof)
            }
            MerkleData::Extension(prover_data) => {
                let (leaf, proof) = merkle_open::<PF<EF>, EF>(prover_data, index);
                (MleOwned::Extension(leaf), proof)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Witness<EF>
where
    EF: ExtensionField<PF<EF>>,
{
    pub prover_data: MerkleData<EF>,
    pub ood_points: Vec<EF>,
    pub ood_answers: Vec<EF>,
}

impl<EF> WhirConfig<EF>
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: TwoAdicField,
{
    #[instrument(skip_all)]
    pub fn commit(
        &self,
        prover_state: &mut impl FSProver<EF>,
        polynomial: &MleOwned<EF>,
        actual_data_len: usize, // polynomial[actual_data_len..] is zero
    ) -> Witness<EF> {
        let n_blocks = 1usize << self.folding_factor.at_round(0);
        let evals_len = 1usize << self.num_variables;
        let effective_n_cols = actual_data_len.div_ceil(evals_len / n_blocks);
        // DFT matrix width: skip as many zero columns as possible, aligned to packing (SIMD)
        let dft_n_cols = effective_n_cols.next_multiple_of(packing_width::<EF>()).min(n_blocks);

        let folded_matrix = info_span!("FFT").in_scope(|| {
            reorder_and_dft(
                &polynomial.by_ref(),
                self.folding_factor.at_round(0),
                self.starting_log_inv_rate,
                dft_n_cols,
            )
        });

        let (prover_data, root) = MerkleData::build(folded_matrix, n_blocks, effective_n_cols);

        prover_state.add_base_scalars(&root);

        // Sample OOD points and evaluate the polynomial at them in parallel.
        // Inlines sample_ood_points so we can dispatch the per-point evaluation
        // through rayon — useful when commitment_ood_samples > 1 because the
        // polynomial buffer is shared across evaluations and stays in cache.
        let (ood_points, ood_answers) = if self.commitment_ood_samples > 0 {
            let pts: Vec<EF> = prover_state.sample_vec(self.commitment_ood_samples);
            use rayon::prelude::*;
            let answers: Vec<EF> = pts
                .par_iter()
                .map(|&p| polynomial.evaluate(&MultilinearPoint::expand_from_univariate(p, self.num_variables)))
                .collect();
            prover_state.add_extension_scalars(&answers);
            (pts, answers)
        } else {
            (Vec::new(), Vec::new())
        };

        Witness {
            prover_data,
            ood_points,
            ood_answers,
        }
    }
}
