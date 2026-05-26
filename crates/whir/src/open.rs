// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

use ::utils::log2_strict_usize;
use fiat_shamir::{FSProver, MerklePath, ProofResult};
use field::{PackedFieldExtension, PrimeCharacteristicRing};
use field::{ExtensionField, Field, TwoAdicField};
use poly::*;
use rayon::prelude::*;
use sumcheck::{
    ProductComputation, fold_and_compute_product_sumcheck_polynomial, run_product_sumcheck,
    sumcheck_prove_many_rounds,
};
use tracing::{info_span, instrument};

use crate::{config::WhirConfig, *};

impl<EF> WhirConfig<EF>
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: TwoAdicField,
{
    fn validate_parameters(&self) -> bool {
        self.num_variables == self.folding_factor.total_number(self.n_rounds()) + self.final_sumcheck_rounds
    }

    fn validate_statement(&self, statement: &[SparseStatement<EF>]) {
        statement.iter().for_each(|e| {
            assert_eq!(e.total_num_variables, self.num_variables);
            assert!(!e.values.is_empty());
            assert!(e.values.iter().all(|v| v.selector < 1 << e.selector_num_variables()));
        });
    }

    fn validate_witness(&self, witness: &Witness<EF>, polynomial: &MleRef<'_, EF>) -> bool {
        assert_eq!(witness.ood_points.len(), witness.ood_answers.len());
        polynomial.n_vars() == self.num_variables
    }

    #[instrument(name = "WHIR prove", skip_all)]
    pub fn prove(
        &self,
        prover_state: &mut impl FSProver<EF>,
        statement: Vec<SparseStatement<EF>>,
        witness: Witness<EF>,
        polynomial: &MleRef<'_, EF>,
    ) -> MultilinearPoint<EF> {
        assert!(self.validate_parameters());
        assert!(self.validate_witness(&witness, polynomial));
        self.validate_statement(&statement);

        let mut round_state =
            RoundState::initialize_first_round_state(self, prover_state, statement, witness, polynomial).unwrap();

        for round in 0..=self.n_rounds() {
            self.round(round, prover_state, &mut round_state).unwrap();
        }

        MultilinearPoint(round_state.randomness_vec)
    }

    fn round(
        &self,
        round_index: usize,
        prover_state: &mut impl FSProver<EF>,
        round_state: &mut RoundState<EF>,
    ) -> ProofResult<()> {
        let folded_evaluations = &round_state.sumcheck_prover.evals;
        let num_variables = self.num_variables - self.folding_factor.total_number(round_index);

        // Base case: final round reached
        if round_index == self.n_rounds() {
            return self.final_round(round_index, prover_state, round_state);
        }

        let round_params = &self.round_parameters[round_index];

        // Compute the folding factors for later use
        let folding_factor_next = self.folding_factor.at_round(round_index + 1);

        // Compute polynomial evaluations and build Merkle tree
        let domain_reduction = 1 << self.rs_reduction_factor(round_index);
        let new_domain_size = round_state.domain_size / domain_reduction;
        let inv_rate = new_domain_size >> num_variables;
        let folded_matrix = info_span!("FFT").in_scope(|| {
            reorder_and_dft(
                &folded_evaluations.by_ref(),
                folding_factor_next,
                log2_strict_usize(inv_rate),
                1 << folding_factor_next,
            )
        });

        let full = 1 << folding_factor_next;
        let (prover_data, root) = MerkleData::build(folded_matrix, full, full);

        prover_state.add_base_scalars(&root);

        // Handle OOD (Out-Of-Domain) samples
        let (ood_points, ood_answers) =
            sample_ood_points::<EF, _>(prover_state, round_params.ood_samples, num_variables, |point| {
                info_span!("ood evaluation").in_scope(|| folded_evaluations.evaluate(point))
            });

        prover_state.pow_grinding(round_params.query_pow_bits);

        let (ood_challenges, stir_challenges, stir_challenges_indexes) = self.compute_stir_queries(
            prover_state,
            round_state,
            num_variables,
            round_params,
            &ood_points,
            round_index,
        )?;

        let folding_randomness = round_state.folding_randomness(
            self.folding_factor.at_round(round_index) + round_state.commitment_merkle_prover_data_b.is_some() as usize,
        );

        let stir_evaluations = if let Some(data_b) = &round_state.commitment_merkle_prover_data_b {
            let answers_a =
                open_merkle_tree_at_challenges(&round_state.merkle_prover_data, prover_state, &stir_challenges_indexes);
            let answers_b = open_merkle_tree_at_challenges(data_b, prover_state, &stir_challenges_indexes);
            let mut stir_evaluations = Vec::new();
            for (answer_a, answer_b) in answers_a.iter().zip(&answers_b) {
                let vars_a = answer_a.by_ref().n_vars();
                let vars_b = answer_b.by_ref().n_vars();
                let a_trunc = folding_randomness[1..].to_vec();
                let eval_a = answer_a.evaluate(&MultilinearPoint(a_trunc));
                let b_trunc = folding_randomness[vars_a - vars_b + 1..].to_vec();
                let eval_b = answer_b.evaluate(&MultilinearPoint(b_trunc));
                let last_fold_rand_a = folding_randomness[0];
                let last_fold_rand_b = folding_randomness[..vars_a - vars_b + 1]
                    .iter()
                    .map(|&x| EF::ONE - x)
                    .product::<EF>();
                stir_evaluations.push(eval_a * last_fold_rand_a + eval_b * last_fold_rand_b);
            }

            stir_evaluations
        } else {
            open_merkle_tree_at_challenges(&round_state.merkle_prover_data, prover_state, &stir_challenges_indexes)
                .iter()
                .map(|answer| answer.evaluate(&folding_randomness))
                .collect()
        };

        // Randomness for combination
        prover_state.duplex();
        let combination_randomness_gen: EF = prover_state.sample();
        let ood_combination_randomness: Vec<_> = combination_randomness_gen.powers().collect_n(ood_challenges.len());
        round_state
            .sumcheck_prover
            .add_new_equality(&ood_challenges, &ood_answers, &ood_combination_randomness);
        let stir_combination_randomness = combination_randomness_gen
            .powers()
            .skip(ood_challenges.len())
            .take(stir_challenges.len())
            .collect::<Vec<_>>();

        round_state.sumcheck_prover.add_new_base_equality(
            &stir_challenges,
            &stir_evaluations,
            &stir_combination_randomness,
        );

        let next_folding_randomness = round_state.sumcheck_prover.run_sumcheck_many_rounds(
            None,
            prover_state,
            folding_factor_next,
            round_params.folding_pow_bits,
        );

        round_state.randomness_vec.extend_from_slice(&next_folding_randomness.0);

        // Update round state
        round_state.domain_size = new_domain_size;
        round_state.next_domain_gen =
            PF::<EF>::two_adic_generator(log2_strict_usize(new_domain_size) - folding_factor_next);
        round_state.merkle_prover_data = prover_data;
        round_state.commitment_merkle_prover_data_b = None;

        Ok(())
    }

    fn final_round(
        &self,
        round_index: usize,
        prover_state: &mut impl FSProver<EF>,
        round_state: &mut RoundState<EF>,
    ) -> ProofResult<()> {
        // Convert evaluations to coefficient form and send to the verifier.
        let mut coeffs = match &round_state.sumcheck_prover.evals {
            MleOwned::Extension(evals) => evals.clone(),
            MleOwned::ExtensionPacked(evals) => unpack_extension::<EF>(evals),
            _ => unreachable!(),
        };
        evals_to_coeffs(&mut coeffs);
        prover_state.add_extension_scalars(&coeffs);

        prover_state.pow_grinding(self.final_query_pow_bits);

        // Final verifier queries and answers. The indices are over the folded domain.
        let final_challenge_indexes = get_challenge_stir_queries(
            // The size of the original domain before folding
            round_state.domain_size >> self.folding_factor.at_round(round_index),
            self.final_queries,
            prover_state,
        );

        let mut base_paths = Vec::new();
        let mut ext_paths = Vec::new();
        for challenge in final_challenge_indexes {
            let (answer, sibling_hashes) = round_state.merkle_prover_data.open(challenge);

            match answer {
                MleOwned::Base(leaf) => {
                    base_paths.push(MerklePath {
                        leaf_data: leaf,
                        sibling_hashes,
                        leaf_index: challenge,
                    });
                }
                MleOwned::Extension(leaf) => {
                    ext_paths.push(MerklePath {
                        leaf_data: leaf,
                        sibling_hashes,
                        leaf_index: challenge,
                    });
                }
                _ => unreachable!(),
            }
        }
        if !base_paths.is_empty() {
            prover_state.hint_merkle_paths_base(base_paths);
        }
        if !ext_paths.is_empty() {
            prover_state.hint_merkle_paths_extension(ext_paths);
        }

        // Run final sumcheck if required
        if self.final_sumcheck_rounds > 0 {
            let final_folding_randomness =
                round_state
                    .sumcheck_prover
                    .run_sumcheck_many_rounds(None, prover_state, self.final_sumcheck_rounds, 0);

            round_state.randomness_vec.extend(final_folding_randomness.0);
        }

        Ok(())
    }

    #[allow(clippy::type_complexity)]
    fn compute_stir_queries(
        &self,
        prover_state: &mut impl FSProver<EF>,
        round_state: &RoundState<EF>,
        num_variables: usize,
        round_params: &RoundConfig<EF>,
        ood_points: &[EF],
        round_index: usize,
    ) -> ProofResult<(Vec<MultilinearPoint<EF>>, Vec<MultilinearPoint<PF<EF>>>, Vec<usize>)> {
        let stir_challenges_indexes = get_challenge_stir_queries(
            round_state.domain_size >> self.folding_factor.at_round(round_index),
            round_params.num_queries,
            prover_state,
        );

        let domain_scaled_gen = round_state.next_domain_gen;
        let ood_challenges = ood_points
            .iter()
            .map(|univariate| MultilinearPoint::expand_from_univariate(*univariate, num_variables))
            .collect();
        let stir_challenges = stir_challenges_indexes
            .iter()
            .map(|i| MultilinearPoint::expand_from_univariate(domain_scaled_gen.exp_u64(*i as u64), num_variables))
            .collect();

        Ok((ood_challenges, stir_challenges, stir_challenges_indexes))
    }
}

fn open_merkle_tree_at_challenges<EF: ExtensionField<PF<EF>>>(
    merkle_tree: &MerkleData<EF>,
    prover_state: &mut impl FSProver<EF>,
    stir_challenges_indexes: &[usize],
) -> Vec<MleOwned<EF>> {
    let mut answers = Vec::new();
    let mut base_paths = Vec::new();
    let mut ext_paths = Vec::new();

    for &challenge in stir_challenges_indexes {
        let (answer, sibling_hashes) = merkle_tree.open(challenge);

        match &answer {
            MleOwned::Base(leaf) => {
                base_paths.push(MerklePath {
                    leaf_data: leaf.clone(),
                    sibling_hashes,
                    leaf_index: challenge,
                });
            }
            MleOwned::Extension(leaf) => {
                ext_paths.push(MerklePath {
                    leaf_data: leaf.clone(),
                    sibling_hashes,
                    leaf_index: challenge,
                });
            }
            _ => unreachable!(),
        }
        answers.push(answer);
    }

    if !base_paths.is_empty() {
        prover_state.hint_merkle_paths_base(base_paths);
    }
    if !ext_paths.is_empty() {
        prover_state.hint_merkle_paths_extension(ext_paths);
    }

    answers
}

#[derive(Debug, Clone)]
pub struct SumcheckSingle<EF: ExtensionField<PF<EF>>> {
    /// Evaluations of the polynomial `p(X)`.
    pub(crate) evals: MleOwned<EF>,
    /// Evaluations of the equality polynomial used for enforcing constraints.
    pub(crate) weights: MleOwned<EF>,
    /// Accumulated sum incorporating equality constraints.
    pub(crate) sum: EF,
}

impl<EF: Field> SumcheckSingle<EF>
where
    EF: ExtensionField<PF<EF>>,
{
    #[instrument(skip_all)]
    pub(crate) fn add_new_equality(
        &mut self,
        points: &[MultilinearPoint<EF>],
        evaluations: &[EF],
        combination_randomness: &[EF],
    ) {
        assert_eq!(combination_randomness.len(), points.len());
        assert_eq!(evaluations.len(), points.len());

        points
            .iter()
            .zip(combination_randomness.iter())
            .for_each(|(point, &rand)| {
                compute_eval_eq_packed::<_, true>(point, self.weights.as_extension_packed_mut().unwrap(), rand);
            });

        self.sum += combination_randomness
            .iter()
            .zip(evaluations.iter())
            .map(|(&rand, &eval)| rand * eval)
            .sum::<EF>();
    }

    #[instrument(skip_all)]
    pub(crate) fn add_new_base_equality(
        &mut self,
        points: &[MultilinearPoint<PF<EF>>],
        evaluations: &[EF],
        combination_randomness: &[EF],
    ) {
        assert_eq!(combination_randomness.len(), points.len());
        assert_eq!(evaluations.len(), points.len());

        compute_eval_eq_base_packed_batched::<PF<EF>, EF>(
            points,
            self.weights.as_extension_packed_mut().unwrap(),
            combination_randomness,
        );

        // Accumulate the weighted sum (cheap, done sequentially)
        self.sum += combination_randomness
            .iter()
            .zip(evaluations.iter())
            .map(|(&rand, &eval)| rand * eval)
            .sum::<EF>();
    }

    fn run_sumcheck_many_rounds(
        &mut self,
        prev_folding_scalar: Option<EF>,
        prover_state: &mut impl FSProver<EF>,
        n_rounds: usize,
        pow_bits: usize,
    ) -> MultilinearPoint<EF> {
        let (challenges, folds, new_sum) = sumcheck_prove_many_rounds(
            MleGroupRef::merge(&[&self.evals.by_ref(), &self.weights.by_ref()]),
            prev_folding_scalar,
            &ProductComputation {},
            &vec![],
            None,
            prover_state,
            self.sum,
            None,
            n_rounds,
            false,
            pow_bits,
        );

        self.sum = new_sum;
        [self.evals, self.weights] = folds.split().try_into().unwrap();

        challenges
    }

    #[instrument(skip_all)]
    pub(crate) fn run_initial_sumcheck_rounds(
        evals: &MleRef<'_, EF>,
        statement: &[SparseStatement<EF>],
        combination_randomness: EF,
        prover_state: &mut impl FSProver<EF>,
        folding_factor: usize,
        pow_bits: usize,
    ) -> (Self, MultilinearPoint<EF>) {
        assert_ne!(folding_factor, 0);

        let packed_evals = evals.pack();

        // Try the fused path: generate weights AND compute round-0 sumcheck
        // polynomial in a single pass over the data.
        let fused_result = match &packed_evals.by_ref() {
            MleRef::BasePacked(packed) => {
                combine_statement_with_round0::<EF>(statement, combination_randomness, packed)
            }
            _ => None,
        };

        if let Some((weights_vec, _sum, first_sumcheck_poly)) = fused_result {
            // Fused path succeeded: weights are generated and round-0 polynomial is computed.
            // Continue with rounds 1+ of the product sumcheck.
            let evals_ref = packed_evals.by_ref();
            let evals_packed = evals_ref.as_packed_base().unwrap();
            let weights_packed = &weights_vec;

            prover_state.add_sumcheck_polynomial(&first_sumcheck_poly.coeffs, None);
            prover_state.pow_grinding(pow_bits);
            let r1: EF = prover_state.sample();
            let mut current_sum = first_sumcheck_poly.evaluate(r1);

            if folding_factor == 1 {
                let folded_evals = MleRef::BasePacked(evals_packed).fold(r1);
                let folded_weights = MleRef::ExtensionPacked(weights_packed).fold(r1);

                let sumcheck = Self {
                    evals: folded_evals,
                    weights: folded_weights,
                    sum: current_sum,
                };
                return (sumcheck, MultilinearPoint(vec![r1]));
            }

            let (second_sumcheck_poly, folded) =
                fold_and_compute_product_sumcheck_polynomial(evals_packed, weights_packed, r1, current_sum, |e| {
                    EFPacking::<EF>::to_ext_iter([e]).collect()
                });

            prover_state.add_sumcheck_polynomial(&second_sumcheck_poly.coeffs, None);
            prover_state.pow_grinding(pow_bits);
            let r2: EF = prover_state.sample();
            current_sum = second_sumcheck_poly.evaluate(r2);

            let (mut challenges, folds, final_sum) = sumcheck_prove_many_rounds(
                MleGroupOwned::ExtensionPacked(folded),
                Some(r2),
                &ProductComputation {},
                &vec![],
                None,
                prover_state,
                current_sum,
                None,
                folding_factor - 2,
                false,
                pow_bits,
            );

            challenges.splice(0..0, [r1, r2]);
            let [new_evals, new_weights]: [MleOwned<EF>; 2] = folds.split().try_into().unwrap();

            let sumcheck = Self {
                evals: new_evals,
                weights: new_weights,
                sum: final_sum,
            };
            (sumcheck, challenges)
        } else {
            // Fallback: use the original two-pass approach.
            let (weights, sum) = combine_statement::<EF>(statement, combination_randomness);

            let mut evals_mle = packed_evals;
            let mut weights_mle = Mle::Owned(MleOwned::ExtensionPacked(weights));
            let (challengess, new_sum, new_evals, new_weights) = run_product_sumcheck(
                &evals_mle.by_ref(),
                &weights_mle.by_ref(),
                prover_state,
                sum,
                folding_factor,
                pow_bits,
            );

            evals_mle = new_evals.into();
            weights_mle = new_weights.into();

            let sumcheck = Self {
                evals: evals_mle.as_owned().unwrap(),
                weights: weights_mle.as_owned().unwrap(),
                sum: new_sum,
            };

            (sumcheck, challengess)
        }
    }
}

#[derive(Debug)]
pub(crate) struct RoundState<EF>
where
    EF: ExtensionField<PF<EF>>,
{
    domain_size: usize,
    next_domain_gen: PF<EF>,
    sumcheck_prover: SumcheckSingle<EF>,
    commitment_merkle_prover_data_b: Option<MerkleData<EF>>,
    merkle_prover_data: MerkleData<EF>,
    randomness_vec: Vec<EF>,
}

#[allow(clippy::mismatching_type_param_order)]
impl<EF> RoundState<EF>
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: TwoAdicField,
{
    pub(crate) fn initialize_first_round_state(
        prover: &WhirConfig<EF>,
        prover_state: &mut impl FSProver<EF>,
        mut statement: Vec<SparseStatement<EF>>,
        witness: Witness<EF>,
        polynomial: &MleRef<'_, EF>,
    ) -> ProofResult<Self> {
        let ood_statements = witness
            .ood_points
            .into_iter()
            .zip(witness.ood_answers)
            .map(|(point, evaluation)| {
                SparseStatement::dense(
                    MultilinearPoint::expand_from_univariate(point, prover.num_variables),
                    evaluation,
                )
            })
            .collect::<Vec<_>>();

        statement.splice(0..0, ood_statements);

        prover_state.duplex();
        let combination_randomness_gen: EF = prover_state.sample();

        let (sumcheck_prover, folding_randomness) = SumcheckSingle::run_initial_sumcheck_rounds(
            polynomial,
            &statement,
            combination_randomness_gen,
            prover_state,
            prover.folding_factor.at_round(0),
            prover.starting_folding_pow_bits,
        );

        Ok(Self {
            domain_size: prover.starting_domain_size(),
            next_domain_gen: PF::<EF>::two_adic_generator(
                log2_strict_usize(prover.starting_domain_size()) - prover.folding_factor.at_round(0),
            ),
            sumcheck_prover,
            merkle_prover_data: witness.prover_data,
            commitment_merkle_prover_data_b: None,
            randomness_vec: folding_randomness.0.clone(),
        })
    }

    fn folding_randomness(&self, folding_factor: usize) -> MultilinearPoint<EF> {
        MultilinearPoint(self.randomness_vec[self.randomness_vec.len() - folding_factor..].to_vec())
    }
}

#[instrument(skip_all, fields(num_constraints = statements.len(), n_vars = statements[0].total_num_variables))]
fn combine_statement<EF>(statements: &[SparseStatement<EF>], gamma: EF) -> (Vec<EFPacking<EF>>, EF)
where
    EF: ExtensionField<PF<EF>>,
{
    let num_variables = statements[0].total_num_variables;
    assert!(statements.iter().all(|e| e.total_num_variables == num_variables));

    let out_len = 1 << (num_variables - packing_log_width::<EF>());

    let first = &statements[0];
    let first_is_full_initializer = !first.is_next
        && first.values.len() == 1
        && first.values[0].selector == 0
        && first.inner_num_variables() == num_variables;

    let mut combined_weights: Vec<EFPacking<EF>>;
    let mut combined_sum = EF::ZERO;
    let mut gamma_pow = EF::ONE;
    let start_idx;

    if first_is_full_initializer {
        combined_weights = unsafe { uninitialized_vec(out_len) };
        let first_scalar = gamma_pow;
        combined_sum += first.values[0].value * gamma_pow;
        gamma_pow *= gamma;

        let second = statements.get(1);
        let second_is_full_domain = second.is_some_and(|s| {
            !s.is_next && s.values.len() == 1 && s.values[0].selector == 0 && s.inner_num_variables() == num_variables
        });

        if second_is_full_domain {
            let second = &statements[1];
            compute_eval_eq_packed_dual::<EF>(
                &first.point.0,
                &second.point.0,
                &mut combined_weights,
                first_scalar,
                gamma_pow,
            );
            combined_sum += second.values[0].value * gamma_pow;
            gamma_pow *= gamma;
            start_idx = 2;
        } else {
            compute_eval_eq_packed::<EF, false>(&first.point.0, &mut combined_weights, first_scalar);
            start_idx = 1;
        }
    } else {
        combined_weights = EFPacking::<EF>::zero_vec(out_len);
        start_idx = 0;
    }

    for smt in &statements[start_idx..] {
        if !smt.is_next && (smt.values.len() == 1 || smt.inner_num_variables() < packing_log_width::<EF>()) {
            for evaluation in &smt.values {
                compute_sparse_eval_eq_packed::<EF>(evaluation.selector, &smt.point, &mut combined_weights, gamma_pow);
                combined_sum += evaluation.value * gamma_pow;
                gamma_pow *= gamma;
            }
        } else {
            let inner_poly = if smt.is_next {
                let next = matrix_next_mle_folded(&smt.point.0);
                pack_extension(&next)
            } else {
                eval_eq_packed(&smt.point)
            };
            let shift = smt.inner_num_variables() - packing_log_width::<EF>();
            let mut indexed_smt_values = smt.values.iter().enumerate().collect::<Vec<_>>();
            indexed_smt_values.sort_by_key(|(_, e)| e.selector);
            indexed_smt_values.dedup_by_key(|(_, e)| e.selector);
            assert_eq!(
                indexed_smt_values.len(),
                smt.values.len(),
                "Duplicate selectors in sparse statement"
            );
            let mut chunks_mut = split_at_mut_many(
                &mut combined_weights,
                &indexed_smt_values
                    .iter()
                    .map(|(_, e)| e.selector << shift)
                    .collect::<Vec<_>>(),
            );
            chunks_mut.remove(0);
            let mut next_gamma_powers = vec![gamma_pow];
            for _ in 1..indexed_smt_values.len() {
                next_gamma_powers.push(*next_gamma_powers.last().unwrap() * gamma);
            }
            for (e, &scalar) in smt.values.iter().zip(&next_gamma_powers) {
                combined_sum += e.value * scalar;
            }
            chunks_mut
                .into_par_iter()
                .zip(&indexed_smt_values)
                .for_each(|(out_buff, &(origin_index, _))| {
                    out_buff[..1 << shift]
                        .par_iter_mut()
                        .zip(&inner_poly)
                        .for_each(|(out_elem, &poly_elem)| {
                            *out_elem += poly_elem * next_gamma_powers[origin_index];
                        });
                });
            gamma_pow = *next_gamma_powers.last().unwrap() * gamma;
        }
    }

    (combined_weights, combined_sum)
}

/// Fused combine_statement + round-0 sumcheck polynomial computation.
///
/// For the common dual-eq path, generates the weight table and computes the
/// round-0 sumcheck polynomial in a single pass, avoiding a separate second
/// pass over the weights array. The remaining sparse statements compute their
/// sumcheck corrections incrementally.
///
/// Returns `None` if the fused path is not applicable (falls back to the
/// original two-pass approach).
#[instrument(skip_all, fields(num_constraints = statements.len(), n_vars = statements[0].total_num_variables))]
fn combine_statement_with_round0<EF>(
    statements: &[SparseStatement<EF>],
    gamma: EF,
    evals: &[PFPacking<EF>],
) -> Option<(Vec<EFPacking<EF>>, EF, DensePolynomial<EF>)>
where
    EF: ExtensionField<PF<EF>>,
{
    let num_variables = statements[0].total_num_variables;
    assert!(statements.iter().all(|e| e.total_num_variables == num_variables));

    let out_len = 1 << (num_variables - packing_log_width::<EF>());
    assert_eq!(evals.len(), out_len);

    let first = &statements[0];
    let first_is_full_initializer = !first.is_next
        && first.values.len() == 1
        && first.values[0].selector == 0
        && first.inner_num_variables() == num_variables;

    if !first_is_full_initializer {
        return None;
    }

    let second = statements.get(1);
    let second_is_full_domain = second.is_some_and(|s| {
        !s.is_next && s.values.len() == 1 && s.values[0].selector == 0 && s.inner_num_variables() == num_variables
    });

    if !second_is_full_domain {
        return None;
    }

    let second = &statements[1];

    let mut combined_sum = EF::ZERO;
    let mut gamma_pow = EF::ONE;

    let first_scalar = gamma_pow;
    combined_sum += first.values[0].value * gamma_pow;
    gamma_pow *= gamma;

    // Fused dual eq generation + round-0 sumcheck dot product.
    let mut combined_weights: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(out_len) };
    let mut round0_poly = compute_eval_eq_packed_dual_with_dotproduct::<PFPacking<EF>, EF>(
        &first.point.0,
        &second.point.0,
        &mut combined_weights,
        first_scalar,
        gamma_pow,
        evals,
        EF::ZERO, // placeholder sum; we'll fix c1 after computing combined_sum
    );

    combined_sum += second.values[0].value * gamma_pow;
    gamma_pow *= gamma;

    let half = out_len / 2;

    // Process remaining statements, applying corrections to the sumcheck polynomial.
    for smt in &statements[2..] {
        if !smt.is_next && (smt.values.len() == 1 || smt.inner_num_variables() < packing_log_width::<EF>()) {
            for evaluation in &smt.values {
                // Compute the eq polynomial delta for this sparse entry.
                // The delta is the eq values that will be added to weights.
                let inner_n_vars = smt.inner_num_variables();
                let log_packing = packing_log_width::<EF>();

                if inner_n_vars < log_packing {
                    // Very small: the modification is sub-packed-element.
                    // Fall back to the original approach for correctness.
                    // Snapshot affected entries, apply modification, compute correction.
                    let packed_idx = evaluation.selector >> (log_packing - inner_n_vars);
                    let old_weight = combined_weights[packed_idx];

                    compute_sparse_eval_eq_packed::<EF>(
                        evaluation.selector,
                        &smt.point,
                        &mut combined_weights,
                        gamma_pow,
                    );

                    let new_weight = combined_weights[packed_idx];
                    let delta = new_weight - old_weight;

                    // Compute sumcheck correction for this single packed element.
                    if packed_idx < half {
                        let paired_idx = packed_idx + half;
                        let e_lo = evals[packed_idx];
                        let e_hi = evals[paired_idx];
                        round0_poly.coeffs[0] += EFPacking::<EF>::to_ext_iter([delta * e_lo]).sum::<EF>();
                        let diff_e = e_hi - e_lo;
                        round0_poly.coeffs[2] -= EFPacking::<EF>::to_ext_iter([delta * diff_e]).sum::<EF>();
                    } else {
                        let paired_idx = packed_idx - half;
                        let e_lo = evals[paired_idx];
                        let e_hi = evals[packed_idx];
                        let diff_e = e_hi - e_lo;
                        round0_poly.coeffs[2] += EFPacking::<EF>::to_ext_iter([delta * diff_e]).sum::<EF>();
                    }
                } else {
                    let region_size = 1 << (inner_n_vars - log_packing);
                    let region_start = evaluation.selector * region_size;

                    // Snapshot the affected region before modification.
                    let old_weights: Vec<EFPacking<EF>> =
                        combined_weights[region_start..region_start + region_size].to_vec();

                    compute_sparse_eval_eq_packed::<EF>(
                        evaluation.selector,
                        &smt.point,
                        &mut combined_weights,
                        gamma_pow,
                    );

                    // Compute sumcheck correction from the delta.
                    sumcheck_correction_for_region(
                        &combined_weights[region_start..region_start + region_size],
                        &old_weights,
                        evals,
                        region_start,
                        half,
                        &mut round0_poly.coeffs,
                    );
                }

                combined_sum += evaluation.value * gamma_pow;
                gamma_pow *= gamma;
            }
        } else {
            let inner_poly = if smt.is_next {
                let next = matrix_next_mle_folded(&smt.point.0);
                pack_extension(&next)
            } else {
                eval_eq_packed(&smt.point)
            };
            let shift = smt.inner_num_variables() - packing_log_width::<EF>();
            let region_size = 1 << shift;
            let mut indexed_smt_values = smt.values.iter().enumerate().collect::<Vec<_>>();
            indexed_smt_values.sort_by_key(|(_, e)| e.selector);
            indexed_smt_values.dedup_by_key(|(_, e)| e.selector);
            assert_eq!(
                indexed_smt_values.len(),
                smt.values.len(),
                "Duplicate selectors in sparse statement"
            );

            let mut next_gamma_powers = vec![gamma_pow];
            for _ in 1..indexed_smt_values.len() {
                next_gamma_powers.push(*next_gamma_powers.last().unwrap() * gamma);
            }
            for (e, &scalar) in smt.values.iter().zip(&next_gamma_powers) {
                combined_sum += e.value * scalar;
            }

            // For each selector region, apply the modification and compute correction.
            for &(origin_index, sv) in &indexed_smt_values {
                let region_start = sv.selector << shift;
                let region_end = region_start + region_size;

                // Snapshot old weights for this region.
                let old_weights: Vec<EFPacking<EF>> =
                    combined_weights[region_start..region_end].to_vec();

                // Apply the modification.
                let scalar = next_gamma_powers[origin_index];
                combined_weights[region_start..region_end]
                    .iter_mut()
                    .zip(&inner_poly)
                    .for_each(|(out_elem, &poly_elem)| {
                        *out_elem += poly_elem * scalar;
                    });

                // Compute sumcheck correction.
                sumcheck_correction_for_region(
                    &combined_weights[region_start..region_end],
                    &old_weights,
                    evals,
                    region_start,
                    half,
                    &mut round0_poly.coeffs,
                );
            }

            gamma_pow = *next_gamma_powers.last().unwrap() * gamma;
        }
    }

    // Fix c1 using the final combined_sum.
    // c0 and c2 are correct, c1 = sum - 2*c0 - c2.
    round0_poly.coeffs[1] = combined_sum - round0_poly.coeffs[0].double() - round0_poly.coeffs[2];

    Some((combined_weights, combined_sum, round0_poly))
}

/// Compute the sumcheck correction when weights in a region change.
///
/// For each position j in [region_start..region_start+region_len]:
///   delta = new_weights[j - region_start] - old_weights[j - region_start]
///   if j < half: c0 += evals[j] * delta; c2 -= (evals[j+half] - evals[j]) * delta
///   if j >= half: c2 += (evals[j] - evals[j-half]) * delta
#[inline]
fn sumcheck_correction_for_region<EF>(
    new_weights: &[EFPacking<EF>],
    old_weights: &[EFPacking<EF>],
    evals: &[PFPacking<EF>],
    region_start: usize,
    half: usize,
    coeffs: &mut [EF],
) where
    EF: ExtensionField<PF<EF>>,
{
    let region_len = new_weights.len();
    debug_assert_eq!(old_weights.len(), region_len);

    let mut c0_acc = EFPacking::<EF>::ZERO;
    let mut c2_acc = EFPacking::<EF>::ZERO;

    for k in 0..region_len {
        let j = region_start + k;
        let delta = new_weights[k] - old_weights[k];

        if j < half {
            let e_lo = evals[j];
            let e_hi = evals[j + half];
            c0_acc += delta * e_lo;
            c2_acc -= delta * (e_hi - e_lo);
        } else {
            let paired = j - half;
            let e_lo = evals[paired];
            let e_hi = evals[j];
            c2_acc += delta * (e_hi - e_lo);
        }
    }

    coeffs[0] += EFPacking::<EF>::to_ext_iter([c0_acc]).sum::<EF>();
    coeffs[2] += EFPacking::<EF>::to_ext_iter([c2_acc]).sum::<EF>();
}