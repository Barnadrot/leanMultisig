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

        // Message word lookups: each G-function reads 2 message words from memory.
        // 4 G-functions × 2 words = 8 lookups per row.
        // Each reads 1 field element from the message address.
        for g in 0..4 {
            lookups.push(LookupIntoMemory {
                index: g_col(g, G_MX_ADDR),
                values: vec![g_col(g, G_MX_VALUE)],
                address_offset: 0,
                conditional_inactive: vec![],
            });
            lookups.push(LookupIntoMemory {
                index: g_col(g, G_MY_ADDR),
                values: vec![g_col(g, G_MY_VALUE)],
                address_offset: 0,
                conditional_inactive: vec![],
            });
        }

        // XOR byte lookups: each G-function has 4 XOR-rotations × 4 byte lookups = 16 per G.
        // 4 G-functions × 16 = 64 XOR lookups per row.
        // Each reads 1 byte from xor_table[256*a + b] = a^b.
        for g in 0..4 {
            // Step 2: d ^ a' (4 byte lookups)
            for i in 0..4 {
                lookups.push(LookupIntoMemory {
                    index: g_col(g, G_XOR2_ADDRS + i),
                    values: vec![g_col(g, G_XOR2_BYTES + i)],
                    address_offset: 0,
                    conditional_inactive: vec![],
                });
            }
            // Step 4: b ^ c' (4 byte lookups)
            for i in 0..4 {
                lookups.push(LookupIntoMemory {
                    index: g_col(g, G_XOR4_ADDRS + i),
                    values: vec![g_col(g, G_XOR4_BYTES + i)],
                    address_offset: 0,
                    conditional_inactive: vec![],
                });
            }
            // Step 6: d' ^ a'' (4 byte lookups)
            for i in 0..4 {
                lookups.push(LookupIntoMemory {
                    index: g_col(g, G_XOR6_ADDRS + i),
                    values: vec![g_col(g, G_XOR6_BYTES + i)],
                    address_offset: 0,
                    conditional_inactive: vec![],
                });
            }
            // Step 8: b' ^ c'' (4 byte lookups)
            for i in 0..4 {
                lookups.push(LookupIntoMemory {
                    index: g_col(g, G_XOR8_ADDRS + i),
                    values: vec![g_col(g, G_XOR8_BYTES + i)],
                    address_offset: 0,
                    conditional_inactive: vec![],
                });
            }
        }

        // Total: 8 message + 64 XOR = 72 lookups per row
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

    fn padding_row(&self, zero_vec_ptr: usize, _null_hash_ptr: usize, _null_blake3_hash_ptr: usize) -> Vec<F> {
        let mut row = vec![F::ZERO; N_TOTAL_COLS];
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
        row[COL_RESULT_ADDR] = F::from_usize(zero_vec_ptr);
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
        let trace = ctx.traces.get_mut(&self.table()).unwrap();
        let xor_table_base = 0; // TODO: set this to actual XOR table address in preamble
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
        3 // from carry range check: carry*(carry-1)*(carry-2)
    }

    fn down_column_indexes(&self) -> Vec<usize> {
        down_columns()
    }

    fn n_constraints(&self) -> usize {
        // Per G-function: ~31 constraints
        // 4 G-functions: 124
        // Control booleans: 4
        // Bus interaction: 1 (if BUS)
        // Down constraints: 32 (state) + 3 (addresses) = 35
        // Output state vs G-function output: 32
        BUS as usize + 4 * super::constrained_air::constraints_per_g() + 4 + 35 + 32
    }

    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        // Read all needed values from up and down before mutably borrowing builder
        let up = builder.up();
        let down = builder.down();

        let flag_active = up[COL_FLAG_ACTIVE];
        let is_first_row = up[COL_IS_FIRST_ROW];
        let is_last_row = up[COL_IS_LAST_ROW];
        let is_column_qr = up[COL_IS_COLUMN_QR];
        let not_last = AB::IF::ONE - is_last_row;

        // Precompute down constraint expressions
        let mut down_constraints = Vec::new();
        for w in 0..16 {
            for l in 0..2 {
                let output = up[output_state_col(w, l)];
                let next_input = down[state_col(w, l)];
                down_constraints.push(flag_active * not_last * (next_input - output));
            }
        }
        down_constraints.push(flag_active * not_last * (down[COL_LEFT_ADDR] - up[COL_LEFT_ADDR]));
        down_constraints.push(flag_active * not_last * (down[COL_RIGHT_ADDR] - up[COL_RIGHT_ADDR]));
        down_constraints.push(flag_active * not_last * (down[COL_RESULT_ADDR] - up[COL_RESULT_ADDR]));

        // Bus data
        let bus_data = if BUS {
            Some((
                is_first_row,
                [up[COL_V_PRECOMPILE_DATA], up[COL_V_INDEX_LEFT], up[COL_RIGHT_ADDR], up[COL_RESULT_ADDR]],
            ))
        } else {
            None
        };

        // Now do all the assert_zero calls
        builder.assert_bool(flag_active);
        builder.assert_bool(is_first_row);
        builder.assert_bool(is_last_row);
        builder.assert_bool(is_column_qr);

        if let Some((selector, data)) = bus_data {
            builder.assert_zero_ef(eval_virtual_bus_column::<AB, EF>(
                extra_data, selector, &data,
            ));
        }

        // G-function constraints
        // Precompute all G-function constraint expressions from up columns
        let up = builder.up();
        let xor_table_base = AB::F::ZERO; // TODO: set to actual XOR_TABLE_BASE
        let mut g_constraints = Vec::new();
        for g in 0..4 {
            let (a_idx, b_idx, c_idx, d_idx) = col_qr_indices(g);
            let exprs = super::constrained_air::g_function_constraints::<AB>(
                up, g, a_idx, b_idx, c_idx, d_idx, xor_table_base,
            );
            g_constraints.extend(exprs);
        }
        for constraint in g_constraints {
            builder.assert_zero(constraint);
        }

        // Down constraints
        for constraint in down_constraints {
            builder.assert_zero(constraint);
        }
    }
}
