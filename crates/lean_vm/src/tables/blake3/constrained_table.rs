/// Full constrained Blake3 precompile table implementation.
///
/// Implements `TableT` (lookups, bus, execute, padding) and `Air` (constraints).
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
/// Default 0 means XOR lookups will point to address 0 (wrong but safe for padding-only tables).
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

    fn lookups(&self) -> Vec<LookupIntoMemory> {
        let mut lookups = Vec::new();
        for g in 0..4 {
            lookups.push(LookupIntoMemory {
                index: g_col(g, G_MX_ADDR),
                values: vec![g_col(g, G_MX_VALUE)],
                address_offset: 0,
                conditional_inactive: vec![],
                computed_address: None,
            });
            lookups.push(LookupIntoMemory {
                index: g_col(g, G_MY_ADDR),
                values: vec![g_col(g, G_MY_VALUE)],
                address_offset: 0,
                conditional_inactive: vec![],
                computed_address: None,
            });
        }

        // XOR byte lookups: verify xor_result = a_byte ^ b_byte via memory[XOR_TABLE_BASE + 256*a + b]
        // Steps 2, 4, 6 use ComputedAddress (no address columns needed).
        // Step 8 keeps explicit address columns (>>>12 byte mapping can't be expressed as a single hi/lo pair).
        let xor_base = get_xor_table_base();
        for g in 0..4 {
            // Step 2: addr = base + 256 * d_byte[i] + add1_byte[i]
            for i in 0..4 {
                lookups.push(LookupIntoMemory {
                    index: 0, // ignored when computed_address is Some
                    values: vec![g_col(g, G_XOR2_BYTES + i)],
                    address_offset: 0,
                    conditional_inactive: vec![],
                    computed_address: Some(ComputedAddress {
                        base: xor_base,
                        hi_col: g_col(g, G_D_BYTES + i),
                        hi_coeff: 256,
                        lo_col: g_col(g, G_ADD1_BYTES + i),
                    }),
                });
            }
            // Step 4: addr = base + 256 * b_byte[i] + add2_byte[i]
            for i in 0..4 {
                lookups.push(LookupIntoMemory {
                    index: 0, // ignored when computed_address is Some
                    values: vec![g_col(g, G_XOR4_BYTES + i)],
                    address_offset: 0,
                    conditional_inactive: vec![],
                    computed_address: Some(ComputedAddress {
                        base: xor_base,
                        hi_col: g_col(g, G_B_BYTES + i),
                        hi_coeff: 256,
                        lo_col: g_col(g, G_ADD2_BYTES + i),
                    }),
                });
            }
            // Step 6: addr = base + 256 * xor2_byte[(i+2)%4] + add3_byte[i]
            for i in 0..4 {
                lookups.push(LookupIntoMemory {
                    index: 0, // ignored when computed_address is Some
                    values: vec![g_col(g, G_XOR6_BYTES + i)],
                    address_offset: 0,
                    conditional_inactive: vec![],
                    computed_address: Some(ComputedAddress {
                        base: xor_base,
                        hi_col: g_col(g, G_XOR2_BYTES + (i + 2) % 4),
                        hi_coeff: 256,
                        lo_col: g_col(g, G_ADD3_BYTES + i),
                    }),
                });
            }
            // Step 8: keeps explicit address columns (>>>12 byte mapping)
            for i in 0..4 {
                lookups.push(LookupIntoMemory {
                    index: g_col(g, G_XOR8_ADDRS + i),
                    values: vec![g_col(g, G_XOR8_BYTES + i)],
                    address_offset: 0,
                    conditional_inactive: vec![],
                    computed_address: None,
                });
            }
        }

        lookups
    }

    fn n_columns_total(&self) -> usize {
        N_TOTAL_COLS
    }

    fn bus(&self) -> Bus {
        Bus {
            direction: BusDirection::Pull,
            selector: COL_IS_FIRST_ROW,
            data: vec![
                BusData::Column(COL_V_PRECOMPILE_DATA),
                BusData::Column(COL_V_INDEX_LEFT),
                BusData::Column(COL_RIGHT_ADDR),
                BusData::Column(COL_RESULT_ADDR),
            ],
        }
    }

    fn padding_row(&self, zero_vec_ptr: usize, _null_hash_ptr: usize, null_blake3_hash_ptr: usize) -> Vec<F> {
        // Start with all zeros — DON'T copy old table padding (it overlaps with G-function columns!)
        let mut row = vec![F::ZERO; N_TOTAL_COLS];
        // Control columns
        row[COL_FLAG_ACTIVE] = F::ZERO;
        row[COL_IS_FIRST_ROW] = F::ZERO;
        row[COL_IS_LAST_ROW] = F::ZERO;
        row[COL_IS_COLUMN_QR] = F::ZERO;
        row[COL_LEFT_ADDR] = F::from_usize(zero_vec_ptr);
        row[COL_RIGHT_ADDR] = F::from_usize(zero_vec_ptr);
        row[COL_RESULT_ADDR] = F::from_usize(null_blake3_hash_ptr);
        // Virtual columns
        row[COL_V_PRECOMPILE_DATA] = F::from_usize(CONSTRAINED_BLAKE3_PRECOMPILE_DATA);
        row[COL_V_INDEX_LEFT] = F::from_usize(zero_vec_ptr);
        // Message lookup addresses
        let xor_base = get_xor_table_base();
        for g in 0..4 {
            row[g_col(g, G_MX_ADDR)] = F::from_usize(zero_vec_ptr);
            row[g_col(g, G_MY_ADDR)] = F::from_usize(zero_vec_ptr);
            // Step 8 XOR lookup addresses: XOR_TABLE_BASE + 256*0 + 0 = XOR_TABLE_BASE
            // (all byte columns are 0 on padding, so xor(0,0) = 0 which matches)
            // Steps 2/4/6 use ComputedAddress — no address columns to fill
            for i in 0..4 {
                row[g_col(g, G_XOR8_ADDRS + i)] = F::from_usize(xor_base);
            }
        }
        // State: all zeros (reads from zero_vec_ptr)
        // G-function columns: all zeros
        // Output state: all zeros
        // Control: inactive
        row[COL_FLAG_ACTIVE] = F::ZERO;
        row[COL_IS_FIRST_ROW] = F::ZERO;
        row[COL_IS_LAST_ROW] = F::ZERO;
        row[COL_IS_COLUMN_QR] = F::ZERO;
        row[COL_LEFT_ADDR] = F::from_usize(zero_vec_ptr);
        row[COL_RIGHT_ADDR] = F::from_usize(zero_vec_ptr);
        row[COL_RESULT_ADDR] = F::from_usize(null_blake3_hash_ptr);
        // Virtual columns
        row[COL_V_INDEX_LEFT] = F::from_usize(zero_vec_ptr);
        row[COL_V_PRECOMPILE_DATA] = F::from_usize(CONSTRAINED_BLAKE3_PRECOMPILE_DATA);
        // Message addresses point to zero vec
        for g in 0..4 {
            row[g_col(g, G_MX_ADDR)] = F::from_usize(zero_vec_ptr);
            row[g_col(g, G_MY_ADDR)] = F::from_usize(zero_vec_ptr);
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

        // Reconstruct the full left input
        let left_addr = left_first_addr; // For non-hardcoded: this is the start of the 8-element input
        let right_addr = arg_b.to_usize();
        let res_addr = index_res.to_usize();

        // Compute blake3 natively
        let arg0_first = ctx.memory.get_slice(left_first_addr, HALF_DIGEST_LEN)?;
        let arg0_second = ctx.memory.get_slice(left_second_addr, HALF_DIGEST_LEN)?;
        let right = ctx.memory.get_slice(right_addr, DIGEST_LEN)?;

        let mut input_left = [F::ZERO; 8];
        input_left[..HALF_DIGEST_LEN].copy_from_slice(&arg0_first);
        input_left[HALF_DIGEST_LEN..].copy_from_slice(&arg0_second);
        let input_right: [F; 8] = right.try_into().unwrap();
        let output = blake3_compress(&input_left, &input_right);

        // Write output to memory
        if half_output {
            ctx.memory.set_slice(res_addr, &output[..HALF_DIGEST_LEN])?;
        } else {
            ctx.memory.set_slice(res_addr, &output)?;
        }

        // Generate the 14-row constrained trace
        eprintln!("Blake3 execute called: left={} right={} res={}", left_addr, right_addr, res_addr);
        let trace = ctx.traces.get_mut(&self.table()).unwrap();
        // XOR table base address: end of preamble minus XOR_TABLE_SIZE
        // This is passed via the preamble memory layout
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
        3 // max constraint degree: carry*(carry-1)*(carry-2)
        // NOTE: the sumcheck uses max_full_degree = max(degree_air+1 across all tables) = 10 (from Poseidon16)
    }

    fn down_column_indexes(&self) -> Vec<usize> {
        down_columns()
    }

    fn n_constraints(&self) -> usize {
        let n_down = if self.down_column_indexes().is_empty() { 0 } else { 35 };
        BUS as usize + 4 * super::constrained_air::constraints_per_g() + 4 + n_down + 8 + 1
    }

    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        // Use NEW column indices for bus constraint
        let up = builder.up();
        let flag_active = up[COL_FLAG_ACTIVE];
        let is_first_row = up[COL_IS_FIRST_ROW];
        let precompile_data: AB::IF = AB::F::from_usize(CONSTRAINED_BLAKE3_PRECOMPILE_DATA).into();
        let bus_selector = is_first_row; // Only first row pulls from bus
        let bus_data = [precompile_data, up[COL_LEFT_ADDR], up[COL_RIGHT_ADDR], up[COL_RESULT_ADDR]];

        if BUS {
            builder.assert_zero_ef(eval_virtual_bus_column::<AB, EF>(
                extra_data, bus_selector, &bus_data,
            ));
        } else {
            builder.declare_values(std::slice::from_ref(&bus_selector));
            builder.declare_values(&bus_data);
        }

        // Boolean constraints
        builder.assert_bool(flag_active);
        let up = builder.up();
        builder.assert_bool(up[COL_IS_FIRST_ROW]);
        let up = builder.up();
        builder.assert_bool(up[COL_IS_LAST_ROW]);
        let up = builder.up();
        builder.assert_bool(up[COL_IS_COLUMN_QR]);

        // G-function constraints
        let up = builder.up();
        let xor_table_base = AB::F::from_usize(get_xor_table_base());
        let mut all_constraints = Vec::new();

        let mut g_outputs = Vec::new();
        for g in 0..4 {
            let (a_idx, b_idx, c_idx, d_idx) = col_qr_indices(g);
            let exprs = super::constrained_air::g_function_constraints::<AB>(
                up, g, a_idx, b_idx, c_idx, d_idx, xor_table_base,
            );
            all_constraints.extend(exprs);

            let (outputs, rot_constraints) = super::constrained_air::g_function_outputs::<AB>(up, g);
            all_constraints.extend(rot_constraints);
            g_outputs.push(outputs);
        }

        for constraint in all_constraints {
            builder.assert_zero(constraint);
        }

        // flag_a_col_qr consistency constraint (degree 2)
        let up = builder.up();
        builder.assert_zero(up[COL_FLAG_A_COL_QR] - up[COL_FLAG_ACTIVE] * up[COL_IS_COLUMN_QR]);

        // Down constraints: link G-function outputs directly to next row's state.
        // Uses COL_FLAG_A_COL_QR (= flag_a * is_column_qr) and (flag_a - flag_a_col_qr)
        // as degree-1 selectors to keep all constraints at degree 3.
        //
        // State word mapping:
        //   Column QR: G_g operates on (a=g, b=g+4, c=g+8, d=g+12)
        //   Diagonal QR: G_g operates on (a=g, b=(g+1)%4+4, c=(g+2)%4+8, d=(g+3)%4+12)
        //
        // For each state word w, we find which G's output it receives in each QR mode.
        {
            let down = builder.down();
            let up = builder.up();
            let mut down_exprs = Vec::new();
            if !down.is_empty() {
                let flag_a = up[COL_FLAG_ACTIVE];
                let not_last = AB::IF::ONE - up[COL_IS_LAST_ROW];
                let flag_col = up[COL_FLAG_A_COL_QR];
                let flag_diag = flag_a - flag_col;

                // Words 0..3 (a-words): both QR types use G_w.a → no mux needed
                for w in 0..4 {
                    let (a_lo, a_hi) = g_outputs[w][0]; // G_w.a output
                    down_exprs.push(flag_a * not_last * (down[w * 2] - a_lo));
                    down_exprs.push(flag_a * not_last * (down[w * 2 + 1] - a_hi));
                }

                // Words 4..7 (b-words): col QR → G_i.b, diag QR → G_{(i+3)%4}.b
                for i in 0..4 {
                    let col_g = i;
                    let diag_g = (i + 3) % 4;
                    let (col_lo, col_hi) = g_outputs[col_g][1];
                    let (diag_lo, diag_hi) = g_outputs[diag_g][1];
                    let w = 4 + i;
                    down_exprs.push(not_last * (flag_col * (down[w * 2] - col_lo) + flag_diag * (down[w * 2] - diag_lo)));
                    down_exprs.push(not_last * (flag_col * (down[w * 2 + 1] - col_hi) + flag_diag * (down[w * 2 + 1] - diag_hi)));
                }

                // Words 8..11 (c-words): col QR → G_i.c, diag QR → G_{(i+2)%4}.c
                for i in 0..4 {
                    let col_g = i;
                    let diag_g = (i + 2) % 4;
                    let (col_lo, col_hi) = g_outputs[col_g][2];
                    let (diag_lo, diag_hi) = g_outputs[diag_g][2];
                    let w = 8 + i;
                    down_exprs.push(not_last * (flag_col * (down[w * 2] - col_lo) + flag_diag * (down[w * 2] - diag_lo)));
                    down_exprs.push(not_last * (flag_col * (down[w * 2 + 1] - col_hi) + flag_diag * (down[w * 2 + 1] - diag_hi)));
                }

                // Words 12..15 (d-words): col QR → G_i.d, diag QR → G_{(i+1)%4}.d
                for i in 0..4 {
                    let col_g = i;
                    let diag_g = (i + 1) % 4;
                    let (col_lo, col_hi) = g_outputs[col_g][3];
                    let (diag_lo, diag_hi) = g_outputs[diag_g][3];
                    let w = 12 + i;
                    down_exprs.push(not_last * (flag_col * (down[w * 2] - col_lo) + flag_diag * (down[w * 2] - diag_lo)));
                    down_exprs.push(not_last * (flag_col * (down[w * 2 + 1] - col_hi) + flag_diag * (down[w * 2 + 1] - diag_hi)));
                }

                // Address down constraints
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
    use backend::get_symbolic_constraints_and_bus_data_values;

    #[test]
    fn test_actual_constraint_count() {
        let table = ConstrainedBlake3Precompile::<false>;
        let (constraints, _bus_flag, _bus_data) = get_symbolic_constraints_and_bus_data_values::<F, _>(&table);
        let expected = table.n_constraints();
        println!("Actual constraints from symbolic eval: {}", constraints.len());
        println!("n_constraints() returns: {}", expected);
        assert_eq!(constraints.len(), expected, "MISMATCH between eval and n_constraints!");
    }
}
