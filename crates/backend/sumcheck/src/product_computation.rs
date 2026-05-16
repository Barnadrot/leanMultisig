use fiat_shamir::*;
use field::*;
use poly::*;
use rayon::prelude::*;
use tracing::instrument;

use crate::{SumcheckComputation, sumcheck_prove_many_rounds};

fn log2_strict(n: usize) -> usize {
    assert!(n.is_power_of_two());
    n.trailing_zeros() as usize
}

#[derive(Debug)]
pub struct ProductComputation;

impl<EF: ExtensionField<PF<EF>>> SumcheckComputation<EF> for ProductComputation {
    type ExtraData = Vec<EF>;

    fn degree(&self) -> usize {
        2
    }
    #[inline(always)]
    fn eval_base(&self, _point: &[PF<EF>], _: &Self::ExtraData) -> EF {
        unreachable!()
    }
    #[inline(always)]
    fn eval_extension(&self, point: &[EF], _: &Self::ExtraData) -> EF {
        point[0] * point[1]
    }
    #[inline(always)]
    fn eval_packed_base(&self, point: &[PFPacking<EF>], _: &Self::ExtraData) -> EFPacking<EF> {
        EFPacking::<EF>::from(point[0] * point[1])
    }
    #[inline(always)]
    fn eval_packed_extension(&self, point: &[EFPacking<EF>], _: &Self::ExtraData) -> EFPacking<EF> {
        point[0] * point[1]
    }
}

#[instrument(skip_all)]
pub fn run_product_sumcheck<EF: ExtensionField<PF<EF>>>(
    pol_a: &MleRef<'_, EF>, // evals
    pol_b: &MleRef<'_, EF>, // weights
    prover_state: &mut impl FSProver<EF>,
    mut sum: EF,
    n_rounds: usize,
    pow_bits: usize,
) -> (MultilinearPoint<EF>, EF, MleOwned<EF>, MleOwned<EF>) {
    assert!(n_rounds >= 1);
    let first_sumcheck_poly = match (pol_a, pol_b) {
        (MleRef::BasePacked(evals), MleRef::ExtensionPacked(weights)) => {
            if EF::DIMENSION == 5 {
                compute_product_sumcheck_polynomial_base_ext_packed::<5, _, _, _, EF>(evals, weights, sum)
            } else {
                unimplemented!()
            }
        }
        (MleRef::ExtensionPacked(evals), MleRef::ExtensionPacked(weights)) => {
            compute_product_sumcheck_polynomial(evals, weights, sum, |e| EFPacking::<EF>::to_ext_iter([e]).collect())
        }
        (MleRef::Base(evals), MleRef::Extension(weights)) => {
            compute_product_sumcheck_polynomial(evals, weights, sum, |e| vec![e])
        }
        (MleRef::Extension(evals), MleRef::Extension(weights)) => {
            compute_product_sumcheck_polynomial(evals, weights, sum, |e| vec![e])
        }
        _ => unimplemented!(),
    };

    prover_state.add_sumcheck_polynomial(&first_sumcheck_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r1: EF = prover_state.sample();
    sum = first_sumcheck_poly.evaluate(r1);

    if n_rounds == 1 {
        return (MultilinearPoint(vec![r1]), sum, pol_a.fold(r1), pol_b.fold(r1));
    }

    let (second_sumcheck_poly, folded) = match (pol_a, pol_b) {
        (MleRef::BasePacked(evals), MleRef::ExtensionPacked(weights)) => {
            let (second_sumcheck_poly, folded) =
                fold_and_compute_product_sumcheck_polynomial(evals, weights, r1, sum, |e| {
                    EFPacking::<EF>::to_ext_iter([e]).collect()
                });
            (second_sumcheck_poly, MleGroupOwned::ExtensionPacked(folded))
        }
        (MleRef::ExtensionPacked(evals), MleRef::ExtensionPacked(weights)) => {
            let (second_sumcheck_poly, folded) =
                fold_and_compute_product_sumcheck_polynomial(evals, weights, r1, sum, |e| {
                    EFPacking::<EF>::to_ext_iter([e]).collect()
                });
            (second_sumcheck_poly, MleGroupOwned::ExtensionPacked(folded))
        }
        (MleRef::Base(evals), MleRef::Extension(weights)) => {
            let (second_sumcheck_poly, folded) =
                fold_and_compute_product_sumcheck_polynomial(evals, weights, r1, sum, |e| vec![e]);
            (second_sumcheck_poly, MleGroupOwned::Extension(folded))
        }
        (MleRef::Extension(evals), MleRef::Extension(weights)) => {
            let (second_sumcheck_poly, folded) =
                fold_and_compute_product_sumcheck_polynomial(evals, weights, r1, sum, |e| vec![e]);
            (second_sumcheck_poly, MleGroupOwned::Extension(folded))
        }
        _ => unimplemented!(),
    };

    prover_state.add_sumcheck_polynomial(&second_sumcheck_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r2: EF = prover_state.sample();
    sum = second_sumcheck_poly.evaluate(r2);

    let (mut challenges, folds, sum) = sumcheck_prove_many_rounds(
        folded,
        Some(r2),
        &ProductComputation {},
        &vec![],
        None,
        prover_state,
        sum,
        None,
        n_rounds - 2,
        false,
        pow_bits,
    );

    challenges.splice(0..0, [r1, r2]);
    let [pol_a, pol_b] = folds.split().try_into().unwrap();
    (challenges, sum, pol_a, pol_b)
}

pub fn compute_product_sumcheck_polynomial<
    F: PrimeCharacteristicRing + Copy + Send + Sync,
    EF: Field,
    EFPacking: Algebra<F> + Copy + Send + Sync,
>(
    pol_0: &[F],         // evals
    pol_1: &[EFPacking], // weights
    sum: EF,
    decompose: impl Fn(EFPacking) -> Vec<EF>,
) -> DensePolynomial<EF> {
    let n = pol_0.len();
    assert_eq!(n, pol_1.len());
    assert!(n.is_power_of_two());

    let num_elements = n;

    let (c0_packed, c2_packed) = if num_elements < PARALLEL_THRESHOLD {
        pol_0[..n / 2]
            .iter()
            .zip(pol_0[n / 2..].iter())
            .zip(pol_1[..n / 2].iter().zip(pol_1[n / 2..].iter()))
            .map(sumcheck_quadratic)
            .fold((EFPacking::ZERO, EFPacking::ZERO), |(a0, a2), (b0, b2)| {
                (a0 + b0, a2 + b2)
            })
    } else {
        pol_0[..n / 2]
            .par_iter()
            .zip(pol_0[n / 2..].par_iter())
            .zip(pol_1[..n / 2].par_iter().zip(pol_1[n / 2..].par_iter()))
            .map(sumcheck_quadratic)
            .reduce(
                || (EFPacking::ZERO, EFPacking::ZERO),
                |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
            )
    };

    let c0 = decompose(c0_packed).into_iter().sum::<EF>();
    let c2 = decompose(c2_packed).into_iter().sum::<EF>();
    let c1 = sum - c0.double() - c2;

    DensePolynomial::new(vec![c0, c1, c2])
}

// using delayed modular reduction
pub fn compute_product_sumcheck_polynomial_base_ext_packed<
    const DIM: usize,
    F: PrimeField32,
    PF: PackedField<Scalar = F>,
    EFP: BasedVectorSpace<PF> + Copy + Send + Sync,
    EF: Field + BasedVectorSpace<F>,
>(
    pol_0: &[PF],
    pol_1: &[EFP],
    sum: EF,
) -> DensePolynomial<EF> {
    assert_eq!(DIM, EF::DIMENSION);
    let n = pol_0.len();
    assert_eq!(n, pol_1.len());
    assert!(n.is_power_of_two());
    let half = n / 2;

    type Acc<const D: usize> = ([u128; D], [i128; D]);

    let chunk_size = 1024;

    let (c0_acc, c2_acc) = pol_0[..half]
        .par_chunks(chunk_size)
        .zip(pol_0[half..].par_chunks(chunk_size))
        .zip(
            pol_1[..half]
                .par_chunks(chunk_size)
                .zip(pol_1[half..].par_chunks(chunk_size)),
        )
        .map(|((b_lo, b_hi), (e_lo, e_hi))| {
            let mut c0 = [0u128; DIM];
            let mut c2 = [0i128; DIM];
            for i in 0..b_lo.len() {
                let x0_lanes = b_lo[i].as_slice();
                let x1_lanes = b_hi[i].as_slice();
                let y0_coords = e_lo[i].as_basis_coefficients_slice();
                let y1_coords = e_hi[i].as_basis_coefficients_slice();
                for j in 0..DIM {
                    let y0_j = y0_coords[j].as_slice();
                    let y1_j = y1_coords[j].as_slice();
                    for lane in 0..PF::WIDTH {
                        let x0 = x0_lanes[lane].to_unique_u32() as u64;
                        let y0 = y0_j[lane].to_unique_u32();
                        let y1 = y1_j[lane].to_unique_u32();
                        c0[j] += (y0 as u64 * x0) as u128;
                        c2[j] += (y1 as i64 - y0 as i64) as i128
                            * (x1_lanes[lane].to_unique_u32() as i64 - x0 as i64) as i128;
                    }
                }
            }
            (c0, c2)
        })
        .reduce(
            || ([0u128; DIM], [0i128; DIM]),
            |(mut a0, mut a2): Acc<DIM>, (b0, b2): Acc<DIM>| {
                for j in 0..DIM {
                    a0[j] += b0[j];
                    a2[j] += b2[j];
                }
                (a0, a2)
            },
        );

    let c0 = EF::from_basis_coefficients_fn(|j| F::reduce_product_sum(c0_acc[j]));
    let c2 = EF::from_basis_coefficients_fn(|j| F::reduce_signed_product_sum(c2_acc[j]));
    let c1 = sum - c0.double() - c2;

    DensePolynomial::new(vec![c0, c1, c2])
}

pub fn fold_and_compute_product_sumcheck_polynomial<
    F: PrimeCharacteristicRing + Copy + Send + Sync + 'static,
    EF: Field,
    EFPacking: Algebra<F> + From<EF> + Copy + Send + Sync + 'static,
>(
    pol_0: &[F],         // evals
    pol_1: &[EFPacking], // weights
    prev_folding_factor: EF,
    sum: EF,
    decompose: impl Fn(EFPacking) -> Vec<EF>,
) -> (DensePolynomial<EF>, Vec<Vec<EFPacking>>) {
    let n = pol_0.len();
    assert_eq!(n, pol_1.len());
    assert!(n.is_power_of_two());
    let prev_folding_factor_packed = EFPacking::from(prev_folding_factor);

    let mut pol_0_folded = unsafe { uninitialized_vec::<EFPacking>(n / 2) };
    let mut pol_1_folded = unsafe { uninitialized_vec::<EFPacking>(n / 2) };

    #[allow(clippy::type_complexity)]
    let process_element = |(p0_prev, p0_f): (((&F, &F), (&F, &F)), (&mut EFPacking, &mut EFPacking)),
                           (p1_prev, p1_f): (
        ((&EFPacking, &EFPacking), (&EFPacking, &EFPacking)),
        (&mut EFPacking, &mut EFPacking),
    )| {
        let diff_0 = *p0_prev.1.0 - *p0_prev.0.0;
        let diff_1 = *p0_prev.1.1 - *p0_prev.0.1;
        let x_0 = prev_folding_factor_packed * diff_0 + *p0_prev.0.0;
        let x_1 = prev_folding_factor_packed * diff_1 + *p0_prev.0.1;
        *p0_f.0 = x_0;
        *p0_f.1 = x_1;

        let y_0 = prev_folding_factor_packed * (*p1_prev.1.0 - *p1_prev.0.0) + *p1_prev.0.0;
        let y_1 = prev_folding_factor_packed * (*p1_prev.1.1 - *p1_prev.0.1) + *p1_prev.0.1;
        *p1_f.0 = y_0;
        *p1_f.1 = y_1;

        sumcheck_quadratic(((&x_0, &x_1), (&y_0, &y_1)))
    };

    let (c0_packed, c2_packed) = if n < PARALLEL_THRESHOLD {
        zip_fold_2(pol_0, &mut pol_0_folded)
            .zip(zip_fold_2(pol_1, &mut pol_1_folded))
            .map(|(p0, p1)| process_element(p0, p1))
            .fold((EFPacking::ZERO, EFPacking::ZERO), |(a0, a2), (b0, b2)| {
                (a0 + b0, a2 + b2)
            })
    } else {
        par_zip_fold_2(pol_0, &mut pol_0_folded)
            .zip(par_zip_fold_2(pol_1, &mut pol_1_folded))
            .map(|(p0, p1)| process_element(p0, p1))
            .reduce(
                || (EFPacking::ZERO, EFPacking::ZERO),
                |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
            )
    };

    let c0 = decompose(c0_packed).into_iter().sum::<EF>();
    let c2 = decompose(c2_packed).into_iter().sum::<EF>();
    let c1 = sum - c0.double() - c2;

    (DensePolynomial::new(vec![c0, c1, c2]), vec![pol_0_folded, pol_1_folded])
}

#[inline(always)]
pub fn sumcheck_quadratic<F, EF>(((&x_0, &x_1), (&y_0, &y_1)): ((&F, &F), (&EF, &EF))) -> (EF, EF)
where
    F: PrimeCharacteristicRing + Copy,
    EF: Algebra<F> + Copy,
{
    let constant = y_0 * x_0;
    let quadratic = (y_1 - y_0) * (x_1 - x_0);
    (constant, quadratic)
}

// --- Fused on-the-fly eq weight evaluation for product sumcheck ---

const LOG_TILE_SIZE: usize = 9;
const TILE_SIZE: usize = 1 << LOG_TILE_SIZE;
pub const LAZY_EQ_MIN_PACKED_VARS: usize = LOG_TILE_SIZE + 3;

pub struct ScatterRegion<EF: ExtensionField<PF<EF>>> {
    pub packed_start: usize,
    pub data: Vec<EFPacking<EF>>,
}

#[instrument(skip_all)]
pub fn run_product_sumcheck_fused_eq<EF: ExtensionField<PF<EF>>>(
    evals: &[PFPacking<EF>],
    point_a: &[EF],
    point_b: &[EF],
    scalar_a: EF,
    scalar_b: EF,
    scatter: &[ScatterRegion<EF>],
    prover_state: &mut impl FSProver<EF>,
    mut sum: EF,
    n_rounds: usize,
    pow_bits: usize,
) -> (MultilinearPoint<EF>, EF, MleOwned<EF>, MleOwned<EF>) {
    assert!(n_rounds >= 2);
    let n = evals.len();
    let half = n / 2;
    let n_packed_vars = log2_strict(n);
    let pw = packing_log_width::<EF>();

    let lane_a = eval_eq_packed_scaled(&point_a[n_packed_vars..], EF::ONE)[0];
    let lane_b = eval_eq_packed_scaled(&point_b[n_packed_vars..], EF::ONE)[0];

    let inner_start = n_packed_vars - LOG_TILE_SIZE;
    let inner_eq_a = eval_eq_scaled(&point_a[inner_start..n_packed_vars], EF::ONE);
    let inner_eq_b = eval_eq_scaled(&point_b[inner_start..n_packed_vars], EF::ONE);

    let inner_a: Vec<EFPacking<EF>> = inner_eq_a.iter().map(|&s| lane_a * s).collect();
    let inner_b: Vec<EFPacking<EF>> = inner_eq_b.iter().map(|&s| lane_b * s).collect();

    // --- ROUND 1 ---
    let outer_eq_a_r1 = eval_eq_scaled(&point_a[1..inner_start], EF::ONE);
    let outer_eq_b_r1 = eval_eq_scaled(&point_b[1..inner_start], EF::ONE);

    let lo_a = scalar_a * (EF::ONE - point_a[0]);
    let hi_a = scalar_a * point_a[0];
    let lo_b = scalar_b * (EF::ONE - point_b[0]);
    let hi_b = scalar_b * point_b[0];

    let (c0_main, c2_main) = compute_lazy_round::<EF>(
        evals, half, &inner_a, &inner_b, &outer_eq_a_r1, &outer_eq_b_r1, lo_a, hi_a, lo_b, hi_b,
    );
    let (c0_scat, c2_scat) = compute_scatter_correction::<EF>(evals, half, scatter);
    let c0 = c0_main + c0_scat;
    let c2 = c2_main + c2_scat;
    let c1 = sum - c0.double() - c2;
    let poly_r1 = DensePolynomial::new(vec![c0, c1, c2]);

    prover_state.add_sumcheck_polynomial(&poly_r1.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r1: EF = prover_state.sample();
    sum = poly_r1.evaluate(r1);

    // --- ROUND 2 ---
    let eq_r1_a = (EF::ONE - r1) * (EF::ONE - point_a[0]) + r1 * point_a[0];
    let eq_r1_b = (EF::ONE - r1) * (EF::ONE - point_b[0]) + r1 * point_b[0];
    let s_a2 = scalar_a * eq_r1_a;
    let s_b2 = scalar_b * eq_r1_b;

    let outer_eq_a_r2 = eval_eq_scaled(&point_a[2..inner_start], EF::ONE);
    let outer_eq_b_r2 = eval_eq_scaled(&point_b[2..inner_start], EF::ONE);

    let lo_a2 = s_a2 * (EF::ONE - point_a[1]);
    let hi_a2 = s_a2 * point_a[1];
    let lo_b2 = s_b2 * (EF::ONE - point_b[1]);
    let hi_b2 = s_b2 * point_b[1];

    let quarter = half / 2;
    let r1_packed = EFPacking::<EF>::from(r1);

    let (c0_main2, c2_main2) = compute_lazy_round_folded::<EF>(
        evals, r1_packed, quarter, &inner_a, &inner_b, &outer_eq_a_r2, &outer_eq_b_r2,
        lo_a2, hi_a2, lo_b2, hi_b2,
    );
    let (c0_scat2, c2_scat2) = compute_scatter_correction_folded::<EF>(evals, r1_packed, quarter, scatter);
    let c0_2 = c0_main2 + c0_scat2;
    let c2_2 = c2_main2 + c2_scat2;
    let c1_2 = sum - c0_2.double() - c2_2;
    let poly_r2 = DensePolynomial::new(vec![c0_2, c1_2, c2_2]);

    prover_state.add_sumcheck_polynomial(&poly_r2.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r2: EF = prover_state.sample();
    sum = poly_r2.evaluate(r2);

    // --- MATERIALIZE r1-FOLDED DATA (n/2 elements) ---
    // Evals: fold base-packed by r1 → extension-packed
    let folded_evals = fold_evals_one_round(evals, r1);

    // Weights: compute eq on remaining vars (point[1..]) with updated scalars
    let remaining_vars = n_packed_vars - 1 + pw;
    let out_len = 1 << (remaining_vars - pw);
    let mut folded_weights = unsafe { uninitialized_vec::<EFPacking<EF>>(out_len) };
    compute_eval_eq_packed_dual::<EF>(
        &point_a[1..1 + remaining_vars],
        &point_b[1..1 + remaining_vars],
        &mut folded_weights,
        s_a2,
        s_b2,
    );

    fold_scatter_into_r1(&mut folded_weights, scatter, r1, half);

    if n_rounds == 2 {
        let folded_evals_r2 = fold_extension_one_round(&folded_evals, r2);
        let folded_weights_r2 = fold_extension_one_round(&folded_weights, r2);
        let challenges = MultilinearPoint(vec![r1, r2]);
        return (challenges, sum, MleOwned::ExtensionPacked(folded_evals_r2), MleOwned::ExtensionPacked(folded_weights_r2));
    }

    let folded = MleGroupOwned::ExtensionPacked(vec![folded_evals, folded_weights]);
    let (mut challenges, folds, sum) = sumcheck_prove_many_rounds(
        folded,
        Some(r2),
        &ProductComputation {},
        &vec![],
        None,
        prover_state,
        sum,
        None,
        n_rounds - 2,
        false,
        pow_bits,
    );

    challenges.0.splice(0..0, [r1, r2]);
    let [pol_a, pol_b] = folds.split().try_into().unwrap();
    (challenges, sum, pol_a, pol_b)
}

fn compute_lazy_round<EF: ExtensionField<PF<EF>>>(
    evals: &[PFPacking<EF>],
    half: usize,
    inner_a: &[EFPacking<EF>],
    inner_b: &[EFPacking<EF>],
    outer_eq_a: &[EF],
    outer_eq_b: &[EF],
    lo_a: EF,
    hi_a: EF,
    lo_b: EF,
    hi_b: EF,
) -> (EF, EF) {
    let n_outer = outer_eq_a.len();
    let diff_a = hi_a - lo_a;
    let diff_b = hi_b - lo_b;

    let (c0_packed, c2_packed): (EFPacking<EF>, EFPacking<EF>) = (0..n_outer)
        .into_par_iter()
        .map(|tile_idx| {
            let outer_lo_a = lo_a * outer_eq_a[tile_idx];
            let outer_lo_b = lo_b * outer_eq_b[tile_idx];
            let outer_diff_a = diff_a * outer_eq_a[tile_idx];
            let outer_diff_b = diff_b * outer_eq_b[tile_idx];

            let base = tile_idx * TILE_SIZE;
            let mut c0_local = EFPacking::<EF>::ZERO;
            let mut c2_local = EFPacking::<EF>::ZERO;

            for j in 0..TILE_SIZE {
                let pos = base + j;
                let eval_lo = evals[pos];
                let eval_hi = evals[pos + half];

                let w_lo = inner_a[j] * outer_lo_a + inner_b[j] * outer_lo_b;
                let w_diff = inner_a[j] * outer_diff_a + inner_b[j] * outer_diff_b;

                c0_local += w_lo * eval_lo;
                c2_local += w_diff * (eval_hi - eval_lo);
            }
            (c0_local, c2_local)
        })
        .reduce(
            || (EFPacking::<EF>::ZERO, EFPacking::<EF>::ZERO),
            |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
        );

    let c0 = EFPacking::<EF>::to_ext_iter([c0_packed]).sum::<EF>();
    let c2 = EFPacking::<EF>::to_ext_iter([c2_packed]).sum::<EF>();
    (c0, c2)
}

fn compute_lazy_round_folded<EF: ExtensionField<PF<EF>>>(
    evals: &[PFPacking<EF>],
    r1_packed: EFPacking<EF>,
    quarter: usize,
    inner_a: &[EFPacking<EF>],
    inner_b: &[EFPacking<EF>],
    outer_eq_a: &[EF],
    outer_eq_b: &[EF],
    lo_a: EF,
    hi_a: EF,
    lo_b: EF,
    hi_b: EF,
) -> (EF, EF) {
    let n_outer = outer_eq_a.len();
    let diff_a = hi_a - lo_a;
    let diff_b = hi_b - lo_b;
    let half = quarter * 2;

    let (c0_packed, c2_packed): (EFPacking<EF>, EFPacking<EF>) = (0..n_outer)
        .into_par_iter()
        .map(|tile_idx| {
            let outer_lo_a = lo_a * outer_eq_a[tile_idx];
            let outer_lo_b = lo_b * outer_eq_b[tile_idx];
            let outer_diff_a = diff_a * outer_eq_a[tile_idx];
            let outer_diff_b = diff_b * outer_eq_b[tile_idx];

            let base = tile_idx * TILE_SIZE;
            let mut c0_local = EFPacking::<EF>::ZERO;
            let mut c2_local = EFPacking::<EF>::ZERO;

            for j in 0..TILE_SIZE {
                let pos = base + j;
                // Fold evals by r1: read from 4 quarters of original
                let e_q0 = evals[pos];
                let e_q1 = evals[pos + quarter];
                let e_q2 = evals[pos + half];
                let e_q3 = evals[pos + half + quarter];

                let folded_lo = r1_packed * (e_q2 - e_q0) + e_q0;
                let folded_hi = r1_packed * (e_q3 - e_q1) + e_q1;

                let w_lo = inner_a[j] * outer_lo_a + inner_b[j] * outer_lo_b;
                let w_diff = inner_a[j] * outer_diff_a + inner_b[j] * outer_diff_b;

                c0_local += w_lo * folded_lo;
                c2_local += w_diff * (folded_hi - folded_lo);
            }
            (c0_local, c2_local)
        })
        .reduce(
            || (EFPacking::<EF>::ZERO, EFPacking::<EF>::ZERO),
            |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
        );

    let c0 = EFPacking::<EF>::to_ext_iter([c0_packed]).sum::<EF>();
    let c2 = EFPacking::<EF>::to_ext_iter([c2_packed]).sum::<EF>();
    (c0, c2)
}

fn compute_scatter_correction<EF: ExtensionField<PF<EF>>>(
    evals: &[PFPacking<EF>],
    half: usize,
    scatter: &[ScatterRegion<EF>],
) -> (EF, EF) {
    if scatter.is_empty() {
        return (EF::ZERO, EF::ZERO);
    }

    scatter
        .par_iter()
        .map(|region| {
            let mut c0 = EFPacking::<EF>::ZERO;
            let mut c2 = EFPacking::<EF>::ZERO;
            for (j, &sw) in region.data.iter().enumerate() {
                let pos = region.packed_start + j;
                if pos < half {
                    let eval_lo = evals[pos];
                    let eval_hi = evals[pos + half];
                    c0 += sw * eval_lo;
                    c2 += sw * (eval_lo - eval_hi);
                } else {
                    let mirror = pos - half;
                    let eval_hi = evals[pos];
                    let eval_lo = evals[mirror];
                    c2 += sw * (eval_hi - eval_lo);
                }
            }
            (
                EFPacking::<EF>::to_ext_iter([c0]).sum::<EF>(),
                EFPacking::<EF>::to_ext_iter([c2]).sum::<EF>(),
            )
        })
        .reduce(|| (EF::ZERO, EF::ZERO), |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2))
}

fn compute_scatter_correction_folded<EF: ExtensionField<PF<EF>>>(
    evals: &[PFPacking<EF>],
    r1_packed: EFPacking<EF>,
    quarter: usize,
    scatter: &[ScatterRegion<EF>],
) -> (EF, EF) {
    if scatter.is_empty() {
        return (EF::ZERO, EF::ZERO);
    }

    let half = quarter * 2;
    scatter
        .par_iter()
        .map(|region| {
            let mut c0 = EFPacking::<EF>::ZERO;
            let mut c2 = EFPacking::<EF>::ZERO;
            for (j, &sw) in region.data.iter().enumerate() {
                let full_pos = region.packed_start + j;
                let lo_pos = full_pos % half;
                let is_hi_half = full_pos >= half;

                let sw_folded = if is_hi_half { sw * r1_packed } else { sw * (EFPacking::<EF>::ONE - r1_packed) };

                if lo_pos < quarter {
                    let e_q0 = evals[lo_pos];
                    let e_q1 = evals[lo_pos + quarter];
                    let folded_lo = r1_packed * (evals[lo_pos + half] - e_q0) + e_q0;
                    let folded_hi = r1_packed * (evals[lo_pos + half + quarter] - e_q1) + e_q1;
                    c0 += sw_folded * folded_lo;
                    c2 += sw_folded * (folded_lo - folded_hi);
                } else {
                    let mirror = lo_pos - quarter;
                    let e_q0 = evals[mirror];
                    let e_q1 = evals[mirror + quarter];
                    let folded_lo = r1_packed * (evals[mirror + half] - e_q0) + e_q0;
                    let folded_hi = r1_packed * (evals[mirror + half + quarter] - e_q1) + e_q1;
                    c2 += sw_folded * (folded_hi - folded_lo);
                }
            }
            (
                EFPacking::<EF>::to_ext_iter([c0]).sum::<EF>(),
                EFPacking::<EF>::to_ext_iter([c2]).sum::<EF>(),
            )
        })
        .reduce(|| (EF::ZERO, EF::ZERO), |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2))
}

fn fold_evals_one_round<EF: ExtensionField<PF<EF>>>(
    evals: &[PFPacking<EF>],
    r1: EF,
) -> Vec<EFPacking<EF>> {
    let n = evals.len();
    let half = n / 2;
    let r1_packed = EFPacking::<EF>::from(r1);

    let mut out = unsafe { uninitialized_vec::<EFPacking<EF>>(half) };
    out.par_iter_mut().enumerate().for_each(|(i, o)| {
        let e_lo = EFPacking::<EF>::from(evals[i]);
        let e_hi = EFPacking::<EF>::from(evals[i + half]);
        *o = r1_packed * (e_hi - e_lo) + e_lo;
    });
    out
}

fn fold_extension_one_round<EF: ExtensionField<PF<EF>>>(
    data: &[EFPacking<EF>],
    r: EF,
) -> Vec<EFPacking<EF>> {
    let n = data.len();
    let half = n / 2;
    let r_packed = EFPacking::<EF>::from(r);

    let mut out = unsafe { uninitialized_vec::<EFPacking<EF>>(half) };
    out.par_iter_mut().enumerate().for_each(|(i, o)| {
        *o = r_packed * (data[i + half] - data[i]) + data[i];
    });
    out
}

fn fold_scatter_into_r1<EF: ExtensionField<PF<EF>>>(
    weights: &mut [EFPacking<EF>],
    scatter: &[ScatterRegion<EF>],
    r1: EF,
    orig_half: usize,
) {
    if scatter.is_empty() {
        return;
    }

    for region in scatter {
        for (j, &sw) in region.data.iter().enumerate() {
            let full_pos = region.packed_start + j;
            let var0_bit = full_pos / orig_half;
            let folded_pos = full_pos % orig_half;

            let factor = if var0_bit == 0 { EF::ONE - r1 } else { r1 };

            if folded_pos < weights.len() {
                weights[folded_pos] += sw * factor;
            }
        }
    }
}
