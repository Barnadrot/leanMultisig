/// Full constrained Blake3 precompile table implementation.
///
/// Implements `TableT` (bus_interactions, execute, padding) and `Air` (constraints).
/// This replaces the unconstrained `Blake3CompressPrecompile` with a fully
/// constrained version that provides 124-bit soundness.

use crate::*;
use crate::execution::memory::MemoryAccess;
use backend::*;
use utils::{ToUsize, blake3_compress};

use super::constrained_cols::*;
use super::constrained_trace::generate_compression_trace;

pub const CONSTRAINED_BLAKE3_PRECOMPILE_DATA: usize = super::BLAKE3_PRECOMPILE_DATA;

use std::sync::atomic::{AtomicUsize, Ordering};

/// XOR table base address in memory. Set at init time by rec_aggregation.
pub static XOR_TABLE_BASE: AtomicUsize = AtomicUsize::new(0);

pub fn set_xor_table_base(addr: usize) {
    XOR_TABLE_BASE.store(addr, Ordering::Relaxed);
}

fn get_xor_table_base() -> usize {
    XOR_TABLE_BASE.load(Ordering::Relaxed)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConstrainedBlake3Precompile<const BUS: bool>;

impl<const BUS: bool> TableT for ConstrainedBlake3Precompile<BUS> {
    fn name(&self) -> &'static str {
        "blake3_compress_constrained"
    }

    fn table(&self) -> Table {
        Table::blake3()
    }

    fn bus_interactions(&self) -> Vec<BusInteraction> {
        let mut buses = Vec::new();

        // Precompile bus (Pull): dispatched by execution table
        buses.push(BusInteraction {
            direction: BusDirection::Pull,
            multiplicity: BusMultiplicity::Column(COL_IS_FIRST_ROW),
            domainsep: BusData::Constant(CONSTRAINED_BLAKE3_PRECOMPILE_DATA),
            data: vec![
                BusData::Column(COL_LEFT_ADDR),
                BusData::Column(COL_RIGHT_ADDR),
                BusData::Column(COL_RESULT_ADDR),
            ],
        });

        // Memory lookups for message words (8 per row: mx and my for 4 G-functions)
        for g in 0..4 {
            buses.push(BusInteraction {
                direction: BusDirection::Push,
                multiplicity: BusMultiplicity::One,
                domainsep: BusData::Constant(LOGUP_MEMORY_DOMAINSEP),
                data: vec![
                    BusData::Column(g_col(g, G_MX_ADDR)),
                    BusData::Column(g_col(g, G_MX_VALUE)),
                ],
            });
            buses.push(BusInteraction {
                direction: BusDirection::Push,
                multiplicity: BusMultiplicity::One,
                domainsep: BusData::Constant(LOGUP_MEMORY_DOMAINSEP),
                data: vec![
                    BusData::Column(g_col(g, G_MY_ADDR)),
                    BusData::Column(g_col(g, G_MY_VALUE)),
                ],
            });
        }

        // XOR byte lookups via memory bus (64 per row: 4 G × 4 steps × 4 bytes)
        // Skip when XOR table not in preamble
        if get_xor_table_base() == 0 { return buses; }
        for g in 0..4 {
            for (xor_addrs, xor_bytes) in [
                (G_XOR2_ADDRS, G_XOR2_BYTES),
                (G_XOR4_ADDRS, G_XOR4_BYTES),
                (G_XOR6_ADDRS, G_XOR6_BYTES),
                (G_XOR8_ADDRS, G_XOR8_BYTES),
            ] {
                for i in 0..4 {
                    buses.push(BusInteraction {
                        direction: BusDirection::Push,
                        multiplicity: BusMultiplicity::One,
                        domainsep: BusData::Constant(LOGUP_MEMORY_DOMAINSEP),
                        data: vec![
                            BusData::Column(g_col(g, xor_addrs + i)),
                            BusData::Column(g_col(g, xor_bytes + i)),
                        ],
                    });
                }
            }
        }

        buses
    }

    fn n_columns_total(&self) -> usize {
        N_TOTAL_COLS
    }

    fn padding_row(&self, zero_vec_ptr: usize, _null_hash_ptr: usize, _ending_pc: usize) -> Vec<F> {
        let null_blake3_hash_ptr = zero_vec_ptr; // Use zero_vec for Blake3 null hash
        let mut row = vec![F::ZERO; N_TOTAL_COLS];
        row[COL_FLAG_ACTIVE] = F::ZERO;
        row[COL_IS_FIRST_ROW] = F::ZERO;
        row[COL_IS_LAST_ROW] = F::ZERO;
        row[COL_IS_COLUMN_QR] = F::ZERO;
        row[COL_LEFT_ADDR] = F::from_usize(zero_vec_ptr);
        row[COL_RIGHT_ADDR] = F::from_usize(zero_vec_ptr);
        row[COL_RESULT_ADDR] = F::from_usize(null_blake3_hash_ptr);
        row[COL_V_PRECOMPILE_DATA] = F::from_usize(CONSTRAINED_BLAKE3_PRECOMPILE_DATA);
        row[COL_V_INDEX_LEFT] = F::from_usize(zero_vec_ptr);
        let xor_base = get_xor_table_base();
        for g in 0..4 {
            row[g_col(g, G_MX_ADDR)] = F::from_usize(zero_vec_ptr);
            row[g_col(g, G_MY_ADDR)] = F::from_usize(zero_vec_ptr);
            for xor_addrs in [G_XOR2_ADDRS, G_XOR4_ADDRS, G_XOR6_ADDRS, G_XOR8_ADDRS] {
                for i in 0..4 {
                    row[g_col(g, xor_addrs + i)] = F::from_usize(xor_base);
                }
            }
        }
        row
    }

    #[inline(always)]
    fn execute<M: MemoryAccess>(
        &self,
        arg_a: F,
        arg_b: F,
        index_res: F,
        args: PrecompileCompTimeArgs<usize>,
        ctx: &mut InstructionContext<'_, M>,
    ) -> Result<(), RunnerError> {
        let PrecompileCompTimeArgs::Blake3Compress {
            half_output,
            hardcoded_offset_left,
        } = args
        else {
            unreachable!("Blake3 table called with non-Blake3 args");
        };

        let arg_a_usize = arg_a.to_usize();
        let flag_hardcoded = hardcoded_offset_left.is_some();
        let left_first_addr = hardcoded_offset_left.unwrap_or(arg_a_usize);
        let left_second_addr = if flag_hardcoded {
            arg_a_usize
        } else {
            arg_a_usize + HALF_DIGEST_LEN
        };

        let left_addr = left_first_addr;
        let right_addr = arg_b.to_usize();
        let res_addr = index_res.to_usize();

        let arg0_first = ctx.memory.get_slice(left_first_addr, HALF_DIGEST_LEN)?;
        let arg0_second = ctx.memory.get_slice(left_second_addr, HALF_DIGEST_LEN)?;
        let right = ctx.memory.get_slice(right_addr, DIGEST_LEN)?;

        let mut input_left = [F::ZERO; 8];
        input_left[..HALF_DIGEST_LEN].copy_from_slice(&arg0_first);
        input_left[HALF_DIGEST_LEN..].copy_from_slice(&arg0_second);
        let input_right: [F; 8] = right.try_into().unwrap();
        let output = blake3_compress(&input_left, &input_right);

        if half_output {
            ctx.memory.set_slice(res_addr, &output[..HALF_DIGEST_LEN])?;
        } else {
            ctx.memory.set_slice(res_addr, &output)?;
        }

        let trace = ctx.traces.get_mut(&self.table()).unwrap();
        let xor_table_base = get_xor_table_base();
        let _trace_output = generate_compression_trace(
            left_addr,
            right_addr,
            res_addr,
            ctx.memory,
            &mut trace.columns,
            xor_table_base,
        )?;

        Ok(())
    }
}

impl<const BUS: bool> Air for ConstrainedBlake3Precompile<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;

    fn n_columns(&self) -> usize {
        N_COMMITTED_COLS
    }

    fn degree_air(&self) -> usize {
        3
    }

    fn n_shift_columns(&self) -> usize {
        35 // 32 state + 3 addresses
    }

    fn down_column_indexes(&self) -> Vec<usize> {
        down_columns()
    }

    fn n_constraints(&self) -> usize {
        let n_down = 35; // always enabled
        BUS as usize + 4 * super::constrained_air::constraints_per_g() + 4 + n_down + 32 + 8
    }

    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let up = builder.up();
        let flag_active = up[COL_FLAG_ACTIVE];
        let is_first_row = up[COL_IS_FIRST_ROW];
        let precompile_data: AB::IF = AB::F::from_usize(CONSTRAINED_BLAKE3_PRECOMPILE_DATA).into();
        let bus_selector = is_first_row;
        let bus_data = [precompile_data, up[COL_LEFT_ADDR], up[COL_RIGHT_ADDR], up[COL_RESULT_ADDR]];

        if BUS {
            eval_bus_virtual::<AB, EF>(
                builder, extra_data, bus_selector, precompile_data, &bus_data,
            );
        } else {
            builder.declare_values(std::slice::from_ref(&bus_selector));
            let mut all_bus_data = vec![precompile_data];
            all_bus_data.extend_from_slice(&bus_data);
            builder.declare_values(&all_bus_data);
        }

        builder.assert_bool(flag_active);
        let up = builder.up();
        builder.assert_bool(up[COL_IS_FIRST_ROW]);
        let up = builder.up();
        builder.assert_bool(up[COL_IS_LAST_ROW]);
        let up = builder.up();
        builder.assert_bool(up[COL_IS_COLUMN_QR]);

        // G-function constraints + output state
        let up = builder.up();
        let xor_table_base = AB::F::from_usize(get_xor_table_base());
        let is_column_qr = up[COL_IS_COLUMN_QR];
        let mut all_constraints = Vec::new();

        for g in 0..4 {
            let (a_idx, b_idx, c_idx, d_idx) = col_qr_indices(g);
            let exprs = super::constrained_air::g_function_constraints::<AB>(
                up, g, a_idx, b_idx, c_idx, d_idx, xor_table_base,
            );
            all_constraints.extend(exprs);

            let (outputs, rot_constraints) = super::constrained_air::g_function_outputs::<AB>(up, g);
            all_constraints.extend(rot_constraints);

            let (a_w, b_w_col, c_w_col, d_w_col) = col_qr_indices(g);
            let (_a_w2, b_w_diag, c_w_diag, d_w_diag) = diag_qr_indices(g);

            let (a_out_lo, a_out_hi) = outputs[0];
            all_constraints.push(up[output_state_col(a_w, 0)] - a_out_lo);
            all_constraints.push(up[output_state_col(a_w, 1)] - a_out_hi);

            for (out_lo, out_hi, w_col, w_diag) in [
                (outputs[1].0, outputs[1].1, b_w_col, b_w_diag),
                (outputs[2].0, outputs[2].1, c_w_col, c_w_diag),
                (outputs[3].0, outputs[3].1, d_w_col, d_w_diag),
            ] {
                if w_col == w_diag {
                    all_constraints.push(up[output_state_col(w_col, 0)] - out_lo);
                    all_constraints.push(up[output_state_col(w_col, 1)] - out_hi);
                } else {
                    all_constraints.push(
                        is_column_qr * (up[output_state_col(w_col, 0)] - out_lo)
                        + (AB::IF::ONE - is_column_qr) * (up[output_state_col(w_diag, 0)] - out_lo)
                    );
                    all_constraints.push(
                        is_column_qr * (up[output_state_col(w_col, 1)] - out_hi)
                        + (AB::IF::ONE - is_column_qr) * (up[output_state_col(w_diag, 1)] - out_hi)
                    );
                }
            }
        }

        for constraint in all_constraints {
            builder.assert_zero(constraint);
        }

        // Down constraints
        {
            let down = builder.down();
            let up = builder.up();
            let mut down_exprs = Vec::new();
            if !down.is_empty() {
                let flag_a = up[COL_FLAG_ACTIVE];
                let not_last = AB::IF::ONE - up[COL_IS_LAST_ROW];
                for w in 0..16 {
                    for l in 0..2 {
                        let output = up[output_state_col(w, l)];
                        let next_input = down[w * 2 + l];
                        down_exprs.push(flag_a * not_last * (next_input - output));
                    }
                }
                let s = 32;
                down_exprs.push(flag_a * not_last * (down[s] - up[COL_LEFT_ADDR]));
                down_exprs.push(flag_a * not_last * (down[s + 1] - up[COL_RIGHT_ADDR]));
                down_exprs.push(flag_a * not_last * (down[s + 2] - up[COL_RESULT_ADDR]));
            }
            for expr in down_exprs {
                builder.assert_zero(expr);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use backend::symbolic::SymbolicAirBuilder;

    #[test]
    fn test_actual_constraint_count() {
        let table = ConstrainedBlake3Precompile::<false>;
        let mut builder = SymbolicAirBuilder::new(table.n_columns(), table.down_column_indexes());
        let extra = ExtraDataForBuses::default();
        table.eval(&mut builder, &extra);
        let actual = builder.constraints().len();
        let expected = table.n_constraints();
        println!("Actual constraints from symbolic eval: {actual}");
        println!("n_constraints() returns: {expected}");
        assert_eq!(actual, expected, "MISMATCH between eval and n_constraints!");
    }
}
