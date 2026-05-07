use tracing::instrument;

use crate::{
    F,
    tables::{Poseidon1Cols16, WIDTH},
};
use backend::*;

#[instrument(name = "generate Poseidon16 AIR trace", skip_all)]
pub fn fill_trace_poseidon_16(trace: &mut [Vec<F>]) {
    let n = trace.iter().map(|col| col.len()).max().unwrap();
    for col in trace.iter_mut() {
        if col.len() != n {
            col.resize(n, F::ZERO);
        }
    }

    let m = n - (n % packing_width::<F>());
    let trace_packed: Vec<_> = trace.iter().map(|col| FPacking::<F>::pack_slice(&col[..m])).collect();

    // fill the packed rows
    (0..m / packing_width::<F>()).into_par_iter().for_each(|i| {
        let ptrs: Vec<*mut FPacking<F>> = trace_packed
            .iter()
            .map(|col| unsafe { (col.as_ptr() as *mut FPacking<F>).add(i) })
            .collect();
        let perm: &mut Poseidon1Cols16<&mut FPacking<F>> =
            unsafe { &mut *(ptrs.as_ptr() as *mut Poseidon1Cols16<&mut FPacking<F>>) };

        generate_trace_rows_for_perm(perm);
    });

    // fill the remaining rows (non packed)
    for i in m..n {
        let ptrs: Vec<*mut F> = trace
            .iter()
            .map(|col| unsafe { (col.as_ptr() as *mut F).add(i) })
            .collect();
        let perm: &mut Poseidon1Cols16<&mut F> = unsafe { &mut *(ptrs.as_ptr() as *mut Poseidon1Cols16<&mut F>) };
        generate_trace_rows_for_perm(perm);
    }
}

pub(super) fn generate_trace_rows_for_perm<F: Algebra<KoalaBear> + Copy>(perm: &mut Poseidon1Cols16<&mut F>) {
    let inputs: [F; WIDTH] = std::array::from_fn(|i| *perm.inputs[i]);
    let mut state = inputs;

    // No initial linear layer for Poseidon1 (unlike Poseidon2)

    // All initial full-round pairs except the last commit a post-MDS witness.
    let n_initial = perm.beginning_full_rounds.len();
    let init_pairs: Vec<_> = poseidon1_initial_constants().chunks_exact(2).collect();
    for (full_round, constants) in perm
        .beginning_full_rounds
        .iter_mut()
        .take(n_initial - 1)
        .zip(init_pairs.iter().take(n_initial - 1))
    {
        generate_2_full_round(&mut state, full_round, &constants[0], &constants[1]);
    }
    // Last initial pair: skip the final MDS so the witness column captures
    // post-cube state (matches the AIR's eval_2_full_rounds_16_no_final_mds).
    {
        let last = n_initial - 1;
        let constants = init_pairs[last];
        generate_2_full_round_no_final_mds(
            &mut state,
            &mut perm.beginning_full_rounds[last],
            &constants[0],
            &constants[1],
        );
    }

    // --- Sparse partial rounds ---
    // Transition: state := (m_i × MDS) × state + (m_i × first_rc).
    let fused = poseidon1_fused_mi_mds();
    let bias = poseidon1_fused_bias();
    let input_for_fused = state;
    for i in 0..WIDTH {
        let row: [F; WIDTH] = fused[i].map(F::from);
        state[i] = F::dot_product(&input_for_fused, &row) + bias[i];
    }

    let first_rows = poseidon1_sparse_first_row();
    let v_vecs = poseidon1_sparse_v();
    let scalar_rc = poseidon1_sparse_scalar_round_constants();
    let n_partial = perm.partial_rounds.len();
    for round in 0..n_partial {
        // S-box on state[0]
        state[0] = state[0].cube();
        *perm.partial_rounds[round] = state[0];
        // Scalar round constant (not on last round)
        if round < n_partial - 1 {
            state[0] += scalar_rc[round];
        }
        // Sparse matrix
        let old_s0 = state[0];
        let row: [F; WIDTH] = first_rows[round].map(F::from);
        let new_s0 = F::dot_product(&state, &row);
        state[0] = new_s0;
        for i in 1..WIDTH {
            state[i] += old_s0 * v_vecs[round][i - 1];
        }
    }

    let n_ending_full_rounds = perm.ending_full_rounds.len();
    for (full_round, constants) in perm
        .ending_full_rounds
        .iter_mut()
        .zip(poseidon1_final_constants().chunks_exact(2))
    {
        generate_2_full_round(&mut state, full_round, &constants[0], &constants[1]);
    }

    // Last 2 full rounds with compression (add inputs to outputs)
    generate_last_2_full_rounds(
        &mut state,
        &inputs,
        &mut perm.outputs,
        &poseidon1_final_constants()[2 * n_ending_full_rounds],
        &poseidon1_final_constants()[2 * n_ending_full_rounds + 1],
    );
}

#[inline]
fn generate_2_full_round<F: Algebra<KoalaBear> + Copy>(
    state: &mut [F; WIDTH],
    post_full_round: &mut [&mut F; WIDTH],
    round_constants_1: &[KoalaBear; WIDTH],
    round_constants_2: &[KoalaBear; WIDTH],
) {
    for (state_i, const_i) in state.iter_mut().zip(round_constants_1) {
        *state_i += *const_i;
        *state_i = state_i.cube();
    }
    mds_circ_16(state);

    for (state_i, const_i) in state.iter_mut().zip(round_constants_2.iter()) {
        *state_i += *const_i;
        *state_i = state_i.cube();
    }
    mds_circ_16(state);

    post_full_round.iter_mut().zip(*state).for_each(|(post, x)| {
        **post = x;
    });
}

/// Same as [`generate_2_full_round`] but skips the final MDS multiply.
/// Used for the last initial full-round pair so the committed witness column
/// captures post-cube state instead of post-MDS state. The skipped MDS is
/// folded into the partial-round transition via `poseidon1_fused_mi_mds`.
#[inline]
fn generate_2_full_round_no_final_mds<F: Algebra<KoalaBear> + Copy>(
    state: &mut [F; WIDTH],
    post_full_round: &mut [&mut F; WIDTH],
    round_constants_1: &[KoalaBear; WIDTH],
    round_constants_2: &[KoalaBear; WIDTH],
) {
    for (state_i, const_i) in state.iter_mut().zip(round_constants_1) {
        *state_i += *const_i;
        *state_i = state_i.cube();
    }
    mds_circ_16(state);

    for (state_i, const_i) in state.iter_mut().zip(round_constants_2.iter()) {
        *state_i += *const_i;
        *state_i = state_i.cube();
    }
    // Final MDS intentionally omitted — see caller.

    post_full_round.iter_mut().zip(*state).for_each(|(post, x)| {
        **post = x;
    });
}

#[inline]
fn generate_last_2_full_rounds<F: Algebra<KoalaBear> + Copy>(
    state: &mut [F; WIDTH],
    inputs: &[F; WIDTH],
    outputs: &mut [&mut F; WIDTH / 2],
    round_constants_1: &[KoalaBear; WIDTH],
    round_constants_2: &[KoalaBear; WIDTH],
) {
    for (state_i, const_i) in state.iter_mut().zip(round_constants_1) {
        *state_i += *const_i;
        *state_i = state_i.cube();
    }
    mds_circ_16(state);

    for (state_i, const_i) in state.iter_mut().zip(round_constants_2.iter()) {
        *state_i += *const_i;
        *state_i = state_i.cube();
    }
    mds_circ_16(state);

    // Add inputs to outputs (compression)
    for ((output, state_i), &input_i) in outputs.iter_mut().zip(state).zip(inputs) {
        **output = *state_i + input_i;
    }
}
