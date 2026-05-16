use std::array;
use std::sync::atomic::{AtomicPtr, Ordering};

use backend::*;
use tracing::instrument;

use crate::{F, poseidon_round_constants};

pub const POSEIDON_16_N_GKR_LAYERS: usize = 29;
pub const POSEIDON_16_N_GKR_COLS: usize = POSEIDON_16_N_GKR_LAYERS * 16;

#[instrument(skip_all)]
pub fn generate_gkr_witness(input_columns: &[Vec<F>]) -> Vec<Vec<F>> {
    const WIDTH: usize = 16;
    assert_eq!(input_columns.len(), WIDTH);
    let n_rows = input_columns[0].len();
    assert!(n_rows.is_power_of_two() && n_rows > packing_width::<F>());
    assert!(input_columns.iter().all(|col| col.len() == n_rows));

    let (initial_constants, partial_constants, final_constants) = poseidon_round_constants::<WIDTH>();
    let n_initial = initial_constants.len();
    let n_partial = partial_constants.len();

    let all_constants: Vec<&[F; WIDTH]> = initial_constants
        .iter()
        .chain(partial_constants.iter())
        .chain(final_constants.iter())
        .collect();
    assert_eq!(all_constants.len(), 28);
    assert_eq!(1 + 28, POSEIDON_16_N_GKR_LAYERS);

    let mut layers: Vec<Vec<F>> = Vec::with_capacity(POSEIDON_16_N_GKR_COLS);
    for _ in 0..POSEIDON_16_N_GKR_COLS {
        layers.push(vec![F::ZERO; n_rows]);
    }

    for j in 0..WIDTH {
        layers[j] = input_columns[j].clone();
        let c = FPacking::<F>::from(all_constants[0][j]);
        for val in FPacking::<F>::pack_slice_mut(&mut layers[j]) {
            *val += c;
        }
    }

    let mut prev_in = 0;
    let mut col = WIDTH;

    for round in 0..28 {
        let next_constants: Option<&[F; WIDTH]> = if round < 27 {
            Some(all_constants[round + 1])
        } else {
            None
        };
        let is_full_round = round < n_initial || round >= n_initial + n_partial;

        {
            let (left, right) = layers.split_at_mut(col);
            let input_slices = &left[prev_in..prev_in + WIDTH];
            let output_slices = &mut right[..WIDTH];
            if is_full_round {
                apply_full_round::<WIDTH>(input_slices, output_slices, next_constants);
            } else {
                apply_partial_round::<WIDTH>(input_slices, output_slices, next_constants);
            }
        }
        prev_in = col;
        col += WIDTH;
    }

    assert_eq!(col, POSEIDON_16_N_GKR_COLS);
    layers
}

pub fn compressed_outputs_from_gkr_witness(
    gkr_witness: &[Vec<F>],
    input_columns: &[Vec<F>],
) -> Vec<Vec<F>> {
    let n_rows = input_columns[0].len();
    let output_layer_start = POSEIDON_16_N_GKR_COLS - 16;
    let mut outputs = Vec::with_capacity(8);
    for i in 0..8 {
        let mut col = vec![F::ZERO; n_rows];
        for row in 0..n_rows {
            col[row] = gkr_witness[output_layer_start + i][row] + input_columns[i][row];
        }
        outputs.push(col);
    }
    outputs
}

fn apply_full_round<const WIDTH: usize>(
    input_cols: &[Vec<F>],
    output_cols: &mut [Vec<F>],
    constants: Option<&[F; WIDTH]>,
) {
    assert_eq!(WIDTH, 16);
    let packed_inputs: [&[FPacking<F>]; WIDTH] = array::from_fn(|i| FPacking::<F>::pack_slice(&input_cols[i]));
    let n_packed = packed_inputs[0].len();

    let mut iter = output_cols.iter_mut();
    let out_ptrs: [AtomicPtr<FPacking<F>>; WIDTH] =
        array::from_fn(|_| AtomicPtr::new(FPacking::<F>::pack_slice_mut(iter.next().unwrap()).as_mut_ptr()));

    (0..n_packed).into_par_iter().for_each(|row| {
        let mut buff: [FPacking<F>; WIDTH] = array::from_fn(|j| packed_inputs[j][row]);
        for v in &mut buff {
            *v = v.cube();
        }
        let buff16: &mut [FPacking<F>; 16] = (&mut buff[..]).try_into().unwrap();
        mds_circ_16(buff16);
        if let Some(constants) = constants {
            for j in 0..WIDTH {
                buff[j] += constants[j];
            }
        }
        for j in 0..WIDTH {
            unsafe { *out_ptrs[j].load(Ordering::Relaxed).add(row) = buff[j] };
        }
    });
}

fn apply_partial_round<const WIDTH: usize>(
    input_cols: &[Vec<F>],
    output_cols: &mut [Vec<F>],
    constants: Option<&[F; WIDTH]>,
) {
    assert_eq!(WIDTH, 16);
    let packed_inputs: [&[FPacking<F>]; WIDTH] = array::from_fn(|i| FPacking::<F>::pack_slice(&input_cols[i]));
    let n_packed = packed_inputs[0].len();

    let mut iter = output_cols.iter_mut();
    let out_ptrs: [AtomicPtr<FPacking<F>>; WIDTH] =
        array::from_fn(|_| AtomicPtr::new(FPacking::<F>::pack_slice_mut(iter.next().unwrap()).as_mut_ptr()));

    (0..n_packed).into_par_iter().for_each(|row| {
        let mut buff: [FPacking<F>; WIDTH] = array::from_fn(|j| packed_inputs[j][row]);
        buff[0] = buff[0].cube();
        let buff16: &mut [FPacking<F>; 16] = (&mut buff[..]).try_into().unwrap();
        mds_circ_16(buff16);
        if let Some(constants) = constants {
            for j in 0..WIDTH {
                buff[j] += constants[j];
            }
        }
        for j in 0..WIDTH {
            unsafe { *out_ptrs[j].load(Ordering::Relaxed).add(row) = buff[j] };
        }
    });
}
