/// Multi-row trace generation for the constrained Blake3 table.
///
/// Each blake3_compress(left, right) call generates 14 trace rows:
/// - 7 rounds × 2 half-rounds (column QR + diagonal QR)
/// - Row state flows via columns that become down-column inputs for the next row
/// - Message words are loaded from memory on the first row

use crate::*;
use crate::execution::memory::MemoryAccess;
use backend::{PrimeCharacteristicRing, PrimeField32};
use utils::ToUsize;

/// Extract the raw Montgomery-form u32 from a KoalaBear field element.
/// MontyField31 is #[repr(transparent)] over u32, so transmute is safe.
#[inline(always)]
fn monty_u32(f: F) -> u32 {
    unsafe { std::mem::transmute::<F, u32>(f) }
}

use super::constrained_cols::*;
use super::g_function::*;

/// Blake3 initial state construction.
/// The 16-word state is: [input_left[0..8] | IV[0..4] | counter_lo, counter_hi, block_len, flags]
/// For Merkle tree hashing (the leanMultisig use case):
/// - chaining value = all zeros (we hash from scratch each time)
/// - counter = 0
/// - block_len = 64
/// - flags = CHUNK_START | CHUNK_END | ROOT = 0x0B
///
/// Actually, leanMultisig's blake3_compress treats left||right as a raw 64-byte
/// input and calls blake3::hash. The Blake3 hash function for a single 64-byte
/// input uses ONE compression with:
/// - h[0..8] = IV (initial chaining value)
/// - m[0..16] = the 16 message words from the input
/// - counter = 0, block_len = 64, flags = CHUNK_START | CHUNK_END | ROOT
fn blake3_initial_state() -> [u32; 16] {
    let mut state = [0u32; 16];
    // h[0..8] = IV
    state[0] = BLAKE3_IV[0];
    state[1] = BLAKE3_IV[1];
    state[2] = BLAKE3_IV[2];
    state[3] = BLAKE3_IV[3];
    state[4] = BLAKE3_IV[4];
    state[5] = BLAKE3_IV[5];
    state[6] = BLAKE3_IV[6];
    state[7] = BLAKE3_IV[7];
    // v[8..12] = IV[0..4]
    state[8] = BLAKE3_IV[0];
    state[9] = BLAKE3_IV[1];
    state[10] = BLAKE3_IV[2];
    state[11] = BLAKE3_IV[3];
    // v[12..16] = counter_lo, counter_hi, block_len, flags
    state[12] = 0;            // counter low
    state[13] = 0;            // counter high
    state[14] = 64;           // block length
    state[15] = 0x0B;         // flags: CHUNK_START | CHUNK_END | ROOT
    state
}

/// Fill the byte decomposition columns for a 32-bit word.
fn fill_word_bytes(row: &mut [Vec<F>], col_start: ColIndex, val: u32) {
    row[col_start].push(F::from_u32(val & 0xFF));
    row[col_start + 1].push(F::from_u32((val >> 8) & 0xFF));
    row[col_start + 2].push(F::from_u32((val >> 16) & 0xFF));
    row[col_start + 3].push(F::from_u32((val >> 24) & 0xFF));
}

/// Fill XOR lookup address columns.
/// address = XOR_TABLE_BASE + 256 * a_byte + b_byte
fn fill_xor_addrs(
    row: &mut [Vec<F>],
    addr_col_start: ColIndex,
    a_val: u32,
    b_val: u32,
    xor_table_base: usize,
) {
    for i in 0..4 {
        let a_byte = (a_val >> (i * 8)) & 0xFF;
        let b_byte = (b_val >> (i * 8)) & 0xFF;
        let addr = xor_table_base + 256 * a_byte as usize + b_byte as usize;
        row[addr_col_start + i].push(F::from_usize(addr));
    }
}

/// Generate the full 14-row trace for one blake3_compress call.
///
/// Returns the 8-element output digest as field elements.
pub fn generate_compression_trace<M: MemoryAccess>(
    left_addr: usize,
    right_addr: usize,
    result_addr: usize,
    memory: &M,
    columns: &mut [Vec<F>],
    xor_table_base: usize,
) -> Result<[F; DIGEST_LEN], RunnerError> {
    // Read inputs from memory
    let left = memory.get_slice(left_addr, 8)?;
    let right = memory.get_slice(right_addr, 8)?;

    // Convert inputs to 32-bit message words (Montgomery form = raw u32)
    // This matches the native blake3_compress which transmutes field elements to bytes
    let mut msg_u32 = [0u32; 16];
    for i in 0..8 {
        msg_u32[i] = monty_u32(left[i]);
        msg_u32[i + 8] = monty_u32(right[i]);
    }

    // Initialize state
    let mut state = blake3_initial_state();

    // Run 7 rounds, each producing 2 rows (column QR + diagonal QR)
    for round in 0..ROUNDS_PER_COMPRESSION {
        let sigma = &BLAKE3_SIGMA[round];

        for qr_type in 0..2 {
            // qr_type 0 = column QR, 1 = diagonal QR
            let is_column_qr = qr_type == 0;
            let is_first_row = round == 0 && qr_type == 0;
            let is_last_row = round == ROUNDS_PER_COMPRESSION - 1 && qr_type == 1;
            let half_round_idx = round * 2 + qr_type;

            // Fill state columns (these become down inputs for next row)
            for w in 0..16 {
                let lo = state[w] & 0xFFFF;
                let hi = state[w] >> 16;
                columns[state_col(w, 0)].push(F::from_u32(lo));
                columns[state_col(w, 1)].push(F::from_u32(hi));
            }

            // Process 4 G-functions
            for g in 0..4 {
                let (a_idx, b_idx, c_idx, d_idx) = if is_column_qr {
                    col_qr_indices(g)
                } else {
                    diag_qr_indices(g)
                };

                // Message word indices for this G-function
                let mx_sigma_idx = if is_column_qr {
                    sigma[2 * g]
                } else {
                    sigma[8 + 2 * g]
                };
                let my_sigma_idx = if is_column_qr {
                    sigma[2 * g + 1]
                } else {
                    sigma[8 + 2 * g + 1]
                };

                let mx = msg_u32[mx_sigma_idx];
                let my = msg_u32[my_sigma_idx];

                // Compute G-function
                let a = state[a_idx];
                let b = state[b_idx];
                let c = state[c_idx];
                let d = state[d_idx];

                let (a_out, b_out, c_out, d_out, trace) =
                    compute_g_function(a, b, c, d, mx, my, xor_table_base);

                // Update state for next half-round
                state[a_idx] = a_out;
                state[b_idx] = b_out;
                state[c_idx] = c_out;
                state[d_idx] = d_out;

                let gc = |offset: usize| -> ColIndex { g_col(g, offset) };

                // Fill G-function columns
                // Step 1: addition result bytes (a')
                fill_word_bytes(columns, gc(G_ADD1_BYTES), trace.add1_result.to_u32());

                // Step 2: d bytes + XOR bytes (addresses computed from G_D_BYTES + G_ADD1_BYTES)
                fill_word_bytes(columns, gc(G_D_BYTES), d);
                let xor2_val = d ^ trace.add1_result.to_u32();
                fill_word_bytes(columns, gc(G_XOR2_BYTES), xor2_val);

                // Step 3: addition result bytes (c')
                fill_word_bytes(columns, gc(G_ADD2_BYTES), trace.add2_result.to_u32());

                // Step 4: b bytes + XOR bytes + split (addresses computed from G_B_BYTES + G_ADD2_BYTES)
                fill_word_bytes(columns, gc(G_B_BYTES), b);
                let xor4_val = b ^ trace.add2_result.to_u32();
                fill_word_bytes(columns, gc(G_XOR4_BYTES), xor4_val);
                // >>>12 nibble split: split xor4_bytes[1] at nibble boundary
                let xor4_b1 = (xor4_val >> 8) & 0xFF;
                columns[gc(G_XOR4_SPLIT)].push(F::from_u32(xor4_b1 & 0x0F));      // lo nibble
                columns[gc(G_XOR4_SPLIT) + 1].push(F::from_u32(xor4_b1 >> 4));     // hi nibble

                // Step 5: addition result bytes (a'')
                fill_word_bytes(columns, gc(G_ADD3_BYTES), trace.add3_result.to_u32());

                // Step 6: XOR bytes (d' bytes reused from xor2, addresses computed from G_XOR2_BYTES + G_ADD3_BYTES)
                let d1 = trace.xor_rot16.result.to_u32();
                let xor6_val = d1 ^ trace.add3_result.to_u32();
                fill_word_bytes(columns, gc(G_XOR6_BYTES), xor6_val);

                // Step 7: addition result bytes (c'')
                fill_word_bytes(columns, gc(G_ADD4_BYTES), trace.add4_result.to_u32());

                // Step 8: XOR bytes + addresses + split (b' bytes reused from xor4)
                let b1 = trace.xor_rot12.result.to_u32();
                let xor8_val = b1 ^ trace.add4_result.to_u32();
                fill_word_bytes(columns, gc(G_XOR8_BYTES), xor8_val);
                fill_xor_addrs(columns, gc(G_XOR8_ADDRS), b1, trace.add4_result.to_u32(), xor_table_base);
                // >>>7 bit split: split xor8_bytes[0] at bit 7
                let xor8_b0 = xor8_val & 0xFF;
                columns[gc(G_XOR8_SPLIT)].push(F::from_u32(xor8_b0 & 0x7F));       // lo 7 bits
                columns[gc(G_XOR8_SPLIT) + 1].push(F::from_u32(xor8_b0 >> 7));     // hi 1 bit

                // Message word columns
                let mx_addr = if mx_sigma_idx < 8 {
                    left_addr + mx_sigma_idx
                } else {
                    right_addr + mx_sigma_idx - 8
                };
                let my_addr = if my_sigma_idx < 8 {
                    left_addr + my_sigma_idx
                } else {
                    right_addr + my_sigma_idx - 8
                };
                // Message value columns: store the ORIGINAL field element from memory
                // (not F::from_u32(monty) which would double-convert)
                let mx_field = if mx_sigma_idx < 8 { left[mx_sigma_idx] } else { right[mx_sigma_idx - 8] };
                let my_field = if my_sigma_idx < 8 { left[my_sigma_idx] } else { right[my_sigma_idx - 8] };
                columns[gc(G_MX_VALUE)].push(mx_field);
                fill_word_bytes(columns, gc(G_MX_BYTES), mx); // bytes of Montgomery u32
                columns[gc(G_MX_ADDR)].push(F::from_usize(mx_addr));
                columns[gc(G_MY_VALUE)].push(my_field);
                fill_word_bytes(columns, gc(G_MY_BYTES), my); // bytes of Montgomery u32
                columns[gc(G_MY_ADDR)].push(F::from_usize(my_addr));

                // Rotation reconstruction columns
                // >>>12 nibble splits for all xor4 bytes that need them
                let xor4_b3 = (xor4_val >> 24) & 0xFF;
                columns[gc(G_XOR4_B3_SPLIT)].push(F::from_u32(xor4_b3 & 0x0F));
                columns[gc(G_XOR4_B3_SPLIT) + 1].push(F::from_u32(xor4_b3 >> 4));
                let xor4_b0_val = xor4_val & 0xFF;
                columns[gc(G_XOR4_B0_SPLIT)].push(F::from_u32(xor4_b0_val & 0x0F));
                columns[gc(G_XOR4_B0_SPLIT) + 1].push(F::from_u32(xor4_b0_val >> 4));
                let xor4_b2_val = (xor4_val >> 16) & 0xFF;
                columns[gc(G_XOR4_B2_SPLIT)].push(F::from_u32(xor4_b2_val & 0x0F));
                columns[gc(G_XOR4_B2_SPLIT) + 1].push(F::from_u32(xor4_b2_val >> 4));

                // >>>7: carry for limb reconstruction
                // b''_lo_raw = split8_hi1 + xor8_b1*2 + xor8_b2*512
                let xor8_b1 = (xor8_val >> 8) & 0xFF;
                let xor8_b2 = (xor8_val >> 16) & 0xFF;
                let split8_hi1 = xor8_b0 >> 7;
                let b2_lo_raw = split8_hi1 + xor8_b1 * 2 + xor8_b2 * 512;
                let carry_rot7 = b2_lo_raw >> 16;
                columns[gc(G_CARRY_ROT7)].push(F::from_u32(carry_rot7));
            }

            // Verify constraint: mx_value * R_CONST = byte_sum for G0
            if cfg!(debug_assertions) {
                let row_idx = columns[0].len() - 1;
                let r_const = F::from_u32(2_164_260_863);
                let mx_val = columns[g_col(0, G_MX_VALUE)][row_idx];
                let mx_b0 = columns[g_col(0, G_MX_BYTES)][row_idx];
                let mx_b1 = columns[g_col(0, G_MX_BYTES + 1)][row_idx];
                let mx_b2 = columns[g_col(0, G_MX_BYTES + 2)][row_idx];
                let mx_b3 = columns[g_col(0, G_MX_BYTES + 3)][row_idx];
                let byte_sum = mx_b0 + mx_b1 * F::from_u32(256) + mx_b2 * F::from_u32(65536) + mx_b3 * F::from_u32(16777216);
                let constraint_val = mx_val * r_const - byte_sum;
                assert_eq!(constraint_val, F::ZERO, "Message decomp constraint failed at row {row_idx}");

                // Check carry constraint: (a_lo + b_lo + mx_lo - result_lo) / 65536 ∈ {0,1,2}
                let a_lo = columns[state_col(0, 0)][row_idx]; // state[0].lo
                let b_b0 = columns[g_col(0, G_B_BYTES)][row_idx];
                let b_b1 = columns[g_col(0, G_B_BYTES + 1)][row_idx];
                let b_lo = b_b0 + b_b1 * F::from_u32(256);
                let mx_lo = mx_b0 + mx_b1 * F::from_u32(256);
                let add1_b0 = columns[g_col(0, G_ADD1_BYTES)][row_idx];
                let add1_b1 = columns[g_col(0, G_ADD1_BYTES + 1)][row_idx];
                let result_lo = add1_b0 + add1_b1 * F::from_u32(256);
                let inv65536 = F::from_u32(2_130_673_921);
                let carry_lo = (a_lo + b_lo + mx_lo - result_lo) * inv65536;
                let two = F::from_u32(2);
                let carry_check = carry_lo * (carry_lo - F::ONE) * (carry_lo - two);
                if carry_check != F::ZERO {
                    eprintln!("CARRY CONSTRAINT FAILED at row {row_idx}!");
                    eprintln!("  a_lo={:?} b_lo={:?} mx_lo={:?} result_lo={:?} carry_lo={:?}",
                        a_lo, b_lo, mx_lo, result_lo, carry_lo);
                    eprintln!("  carry_check={:?}", carry_check);
                    panic!("Carry constraint failed");
                }
            }

            // Fill control columns
            columns[COL_FLAG_ACTIVE].push(F::ONE);
            columns[COL_IS_FIRST_ROW].push(F::from_bool(is_first_row));
            columns[COL_IS_LAST_ROW].push(F::from_bool(is_last_row));
            columns[COL_IS_COLUMN_QR].push(F::from_bool(is_column_qr));
            columns[COL_LEFT_ADDR].push(F::from_usize(left_addr));
            columns[COL_RIGHT_ADDR].push(F::from_usize(right_addr));
            columns[COL_RESULT_ADDR].push(F::from_usize(result_addr));
            columns[COL_FLAG_A_COL_QR].push(F::from_bool(is_column_qr)); // flag_active=1 here, so flag_a * is_col_qr = is_col_qr

            // Virtual columns
            columns[COL_V_INDEX_LEFT].push(F::from_usize(left_addr));
            columns[COL_V_PRECOMPILE_DATA].push(F::from_usize(super::BLAKE3_PRECOMPILE_DATA));
        }
    }

    // Compute output: first 8 words of final state XORed with last 8
    // (Blake3 finalization: h[i] = v[i] ^ v[i+8])
    let mut output = [F::ZERO; DIGEST_LEN];
    for i in 0..8 {
        let finalized = state[i] ^ state[i + 8];
        // Convert back to field element (mod p)
        output[i] = F::from_u32(finalized % F::ORDER_U32);
    }

    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;
    use backend::PrimeField32;

    use utils::blake3_compress;

    struct SimpleMemory(Vec<F>);
    impl MemoryAccess for SimpleMemory {
        fn get(&self, addr: usize) -> Result<F, RunnerError> {
            self.0.get(addr).copied().ok_or(RunnerError::UndefinedMemory(addr))
        }
        fn set(&mut self, addr: usize, val: F) -> Result<(), RunnerError> {
            if addr >= self.0.len() { self.0.resize(addr + 1, F::ZERO); }
            self.0[addr] = val;
            Ok(())
        }
    }

    #[test]
    fn test_trace_matches_native() {
        let left = [F::from_u32(1), F::from_u32(2), F::from_u32(3), F::from_u32(4),
                     F::from_u32(5), F::from_u32(6), F::from_u32(7), F::from_u32(8)];
        let right = [F::from_u32(9), F::from_u32(10), F::from_u32(11), F::from_u32(12),
                      F::from_u32(13), F::from_u32(14), F::from_u32(15), F::from_u32(16)];

        // Native blake3_compress (Montgomery-form transmute) — trace must match
        let expected = blake3_compress(&left, &right);

        // Trace-based blake3_compress
        let mut mem = SimpleMemory(vec![F::ZERO; 100]);
        for i in 0..8 {
            mem.0[i] = left[i];
            mem.0[8 + i] = right[i];
        }
        let mut columns: Vec<Vec<F>> = vec![Vec::new(); N_TOTAL_COLS];
        let output = generate_compression_trace(
            0, 8, 50, &mem, &mut columns, 0,
        ).unwrap();

        // Verify output matches
        for i in 0..8 {
            assert_eq!(output[i], expected[i],
                "Output mismatch at index {i}: trace={:?} native={:?}",
                output[i], expected[i]);
        }

        // Verify 14 rows were generated
        assert_eq!(columns[COL_FLAG_ACTIVE].len(), ROWS_PER_COMPRESSION);

        // Verify first/last row flags
        assert_eq!(columns[COL_IS_FIRST_ROW][0], F::ONE);
        for r in 1..ROWS_PER_COMPRESSION {
            assert_eq!(columns[COL_IS_FIRST_ROW][r], F::ZERO);
        }
        assert_eq!(columns[COL_IS_LAST_ROW][ROWS_PER_COMPRESSION - 1], F::ONE);
        for r in 0..ROWS_PER_COMPRESSION - 1 {
            assert_eq!(columns[COL_IS_LAST_ROW][r], F::ZERO);
        }

        // Verify column/diagonal QR alternation
        for r in 0..ROWS_PER_COMPRESSION {
            let expected_qr = if r % 2 == 0 { F::ONE } else { F::ZERO };
            assert_eq!(columns[COL_IS_COLUMN_QR][r], expected_qr,
                "QR flag mismatch at row {r}");
        }
    }
}
