use fiat_shamir::*;
use field::*;
use poly::*;
use rayon::prelude::*;
use tracing::instrument;

use crate::{SumcheckComputation, sumcheck_prove_many_rounds};

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
            compute_product_sumcheck_polynomial(evals, weights, sum, |e| EFPacking::<EF>::to_ext_iter([e]).collect())
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

pub struct FactoredWeights<EF: ExtensionField<PF<EF>>> {
    pub eq_top_a: Vec<EF>,
    pub eq_top_b: Vec<EF>,
    pub eq_bot_a: Vec<EFPacking<EF>>,
    pub eq_bot_b: Vec<EFPacking<EF>>,
    pub corrections: Vec<EFPacking<EF>>,
}

#[instrument(skip_all)]
pub fn run_product_sumcheck_factored<EF: ExtensionField<PF<EF>>>(
    evals: &[PFPacking<EF>],
    factored: FactoredWeights<EF>,
    prover_state: &mut impl FSProver<EF>,
    mut sum: EF,
    n_rounds: usize,
    pow_bits: usize,
) -> (MultilinearPoint<EF>, EF, MleOwned<EF>, MleOwned<EF>) {
    assert!(n_rounds >= 1);

    let n_bot = factored.eq_bot_a.len();
    let n_top = factored.eq_top_a.len();
    let n = evals.len();
    assert_eq!(n, n_top * n_bot);
    assert_eq!(n, factored.corrections.len());
    assert!(n_top.is_power_of_two());
    assert!(n_bot.is_power_of_two());

    let (c0_packed, c2_packed) = compute_factored_round_poly_base(evals, &factored, n_top, n_bot);
    let c0: EF = EFPacking::<EF>::to_ext_iter([c0_packed]).collect::<Vec<_>>().into_iter().sum();
    let c2: EF = EFPacking::<EF>::to_ext_iter([c2_packed]).collect::<Vec<_>>().into_iter().sum();
    let c1 = sum - c0.double() - c2;
    let first_sumcheck_poly = DensePolynomial::new(vec![c0, c1, c2]);

    prover_state.add_sumcheck_polynomial(&first_sumcheck_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r1: EF = prover_state.sample();
    sum = first_sumcheck_poly.evaluate(r1);

    let weights_folded = materialize_and_fold_factored(&factored, n_top, n_bot, r1);
    let evals_folded = fold_base_packed(evals, r1);

    if n_rounds == 1 {
        return (
            MultilinearPoint(vec![r1]),
            sum,
            MleOwned::ExtensionPacked(evals_folded),
            MleOwned::ExtensionPacked(weights_folded),
        );
    }

    let second_sumcheck_poly = compute_product_sumcheck_polynomial(
        &evals_folded,
        &weights_folded,
        sum,
        |e| EFPacking::<EF>::to_ext_iter([e]).collect(),
    );

    prover_state.add_sumcheck_polynomial(&second_sumcheck_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r2: EF = prover_state.sample();
    sum = second_sumcheck_poly.evaluate(r2);

    if n_rounds == 2 {
        let evals_folded2 = fold_ext_packed(&evals_folded, r2);
        let weights_folded2 = fold_ext_packed(&weights_folded, r2);
        return (
            MultilinearPoint(vec![r1, r2]),
            sum,
            MleOwned::ExtensionPacked(evals_folded2),
            MleOwned::ExtensionPacked(weights_folded2),
        );
    }

    let (third_poly, folded) =
        fold_and_compute_product_sumcheck_polynomial(
            &evals_folded, &weights_folded, r2, sum,
            |e| EFPacking::<EF>::to_ext_iter([e]).collect(),
        );
    let folded = MleGroupOwned::ExtensionPacked(folded);

    prover_state.add_sumcheck_polynomial(&third_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r3: EF = prover_state.sample();
    sum = third_poly.evaluate(r3);

    if n_rounds == 3 {
        let [pol_a, pol_b] = folded.split().try_into().unwrap();
        return (MultilinearPoint(vec![r1, r2, r3]), sum, pol_a, pol_b);
    }

    let (mut challenges, folds, sum) = sumcheck_prove_many_rounds(
        folded,
        Some(r3),
        &ProductComputation {},
        &vec![],
        None,
        prover_state,
        sum,
        None,
        n_rounds - 3,
        false,
        pow_bits,
    );

    challenges.splice(0..0, [r1, r2, r3]);
    let [pol_a, pol_b] = folds.split().try_into().unwrap();
    (challenges, sum, pol_a, pol_b)
}

fn fold_base_packed<EF: ExtensionField<PF<EF>>>(
    evals: &[PFPacking<EF>],
    r: EF,
) -> Vec<EFPacking<EF>> {
    let half = evals.len() / 2;
    let r_packed = EFPacking::<EF>::from(r);
    let mut out: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(half) };
    out.par_iter_mut().enumerate().for_each(|(i, o)| {
        let lo = EFPacking::<EF>::from(evals[i]);
        let hi = EFPacking::<EF>::from(evals[i + half]);
        *o = r_packed * (hi - lo) + lo;
    });
    out
}

fn fold_ext_packed<EF: ExtensionField<PF<EF>>>(
    data: &[EFPacking<EF>],
    r: EF,
) -> Vec<EFPacking<EF>> {
    let half = data.len() / 2;
    let r_packed = EFPacking::<EF>::from(r);
    let mut out: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(half) };
    out.par_iter_mut().enumerate().for_each(|(i, o)| {
        *o = r_packed * (data[i + half] - data[i]) + data[i];
    });
    out
}

fn materialize_and_fold_factored<EF: ExtensionField<PF<EF>>>(
    factored: &FactoredWeights<EF>,
    n_top: usize,
    n_bot: usize,
    r: EF,
) -> Vec<EFPacking<EF>> {
    let half_top = n_top / 2;
    let total_folded = half_top * n_bot;
    let r_packed = EFPacking::<EF>::from(r);
    let mut weights: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(total_folded) };

    weights.par_chunks_mut(n_bot).enumerate().for_each(|(j, chunk)| {
        let a_lo = EFPacking::<EF>::from(factored.eq_top_a[j]);
        let a_hi = EFPacking::<EF>::from(factored.eq_top_a[j + half_top]);
        let b_lo = EFPacking::<EF>::from(factored.eq_top_b[j]);
        let b_hi = EFPacking::<EF>::from(factored.eq_top_b[j + half_top]);
        let a_folded = r_packed * (a_hi - a_lo) + a_lo;
        let b_folded = r_packed * (b_hi - b_lo) + b_lo;
        for (t, w) in chunk.iter_mut().enumerate() {
            let w_factored = a_folded * factored.eq_bot_a[t] + b_folded * factored.eq_bot_b[t];
            let c_lo = factored.corrections[j * n_bot + t];
            let c_hi = factored.corrections[(j + half_top) * n_bot + t];
            let c_folded = r_packed * (c_hi - c_lo) + c_lo;
            *w = w_factored + c_folded;
        }
    });

    weights
}

fn compute_factored_round_poly_base<EF: ExtensionField<PF<EF>>>(
    evals: &[PFPacking<EF>],
    factored: &FactoredWeights<EF>,
    n_top: usize,
    n_bot: usize,
) -> (EFPacking<EF>, EFPacking<EF>) {
    let half_top = n_top / 2;
    let n = evals.len();
    assert_eq!(n, n_top * n_bot);

    const TILE_SIZE: usize = 1024;
    let n_tiles = (n_bot + TILE_SIZE - 1) / TILE_SIZE;

    let (c0_total, c2_total) = (0..n_tiles)
        .into_par_iter()
        .map(|tile_idx| {
            let tile_start = tile_idx * TILE_SIZE;
            let tile_len = TILE_SIZE.min(n_bot - tile_start);

            let mut acc_c0_a = vec![EFPacking::<EF>::ZERO; tile_len];
            let mut acc_c0_b = vec![EFPacking::<EF>::ZERO; tile_len];
            let mut acc_c2_a = vec![EFPacking::<EF>::ZERO; tile_len];
            let mut acc_c2_b = vec![EFPacking::<EF>::ZERO; tile_len];
            let mut acc_corr_c0 = vec![EFPacking::<EF>::ZERO; tile_len];
            let mut acc_corr_c2 = vec![EFPacking::<EF>::ZERO; tile_len];

            for j in 0..half_top {
                let top_a_lo = EFPacking::<EF>::from(factored.eq_top_a[j]);
                let top_a_hi = EFPacking::<EF>::from(factored.eq_top_a[j + half_top]);
                let top_b_lo = EFPacking::<EF>::from(factored.eq_top_b[j]);
                let top_b_hi = EFPacking::<EF>::from(factored.eq_top_b[j + half_top]);
                let da_j = top_a_hi - top_a_lo;
                let db_j = top_b_hi - top_b_lo;

                let evals_lo_base = j * n_bot + tile_start;
                let evals_hi_base = (j + half_top) * n_bot + tile_start;

                for t in 0..tile_len {
                    let e_lo = evals[evals_lo_base + t];
                    let e_hi = evals[evals_hi_base + t];
                    acc_c0_a[t] += top_a_lo * e_lo;
                    acc_c0_b[t] += top_b_lo * e_lo;
                    let e_diff = e_hi - e_lo;
                    acc_c2_a[t] += da_j * e_diff;
                    acc_c2_b[t] += db_j * e_diff;
                    acc_corr_c0[t] += factored.corrections[evals_lo_base + t] * e_lo;
                    acc_corr_c2[t] += (factored.corrections[evals_hi_base + t]
                        - factored.corrections[evals_lo_base + t])
                        * e_diff;
                }
            }

            let mut c0 = EFPacking::<EF>::ZERO;
            let mut c2 = EFPacking::<EF>::ZERO;
            for t in 0..tile_len {
                let idx = tile_start + t;
                let bot_a = factored.eq_bot_a[idx];
                let bot_b = factored.eq_bot_b[idx];

                c0 += acc_c0_a[t] * bot_a + acc_c0_b[t] * bot_b + acc_corr_c0[t];
                c2 += acc_c2_a[t] * bot_a + acc_c2_b[t] * bot_b + acc_corr_c2[t];
            }

            (c0, c2)
        })
        .reduce(
            || (EFPacking::<EF>::ZERO, EFPacking::<EF>::ZERO),
            |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
        );

    (c0_total, c2_total)
}