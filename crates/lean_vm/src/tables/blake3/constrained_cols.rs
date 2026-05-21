/// Column layout for the constrained Blake3 table.
///
/// 14 rows per compression (1 half-round per row, 2 half-rounds per round, 7 rounds).
/// Each row processes 4 G-functions (either column or diagonal quarter-round).
///
/// Message schedule correctness is implied by end-to-end Merkle verification:
/// message word addresses are columns filled by the prover; the memory bus
/// verifies reads, and incorrect messages produce wrong outputs that fail
/// the Merkle path check.

use super::g_function::*;
use crate::tables::table_trait::ColIndex;

// ─── Blake3 message schedule (SIGMA) ─────────────────────────────────────────

/// Blake3 message schedule: SIGMA[round][i] gives the message word index
/// for the i-th position in round `round`.
/// Positions 0-7 are for the column quarter-round, 8-15 for diagonal.
pub const BLAKE3_SIGMA: [[usize; 16]; 7] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8],
    [3, 4, 10, 12, 13, 2, 7, 14, 6, 5, 9, 0, 11, 15, 8, 1],
    [10, 7, 12, 9, 14, 3, 13, 15, 4, 0, 11, 2, 5, 8, 1, 6],
    [12, 13, 9, 11, 15, 10, 14, 8, 7, 2, 5, 3, 0, 1, 6, 4],
    [9, 14, 11, 5, 8, 12, 15, 1, 13, 3, 0, 10, 2, 6, 4, 7],
    [11, 15, 5, 0, 1, 9, 8, 6, 14, 10, 2, 12, 3, 4, 7, 13],
];

// ─── Blake3 IV ───────────────────────────────────────────────────────────────

/// Blake3 initialization vector (first 8 words of SHA-256 IV).
pub const BLAKE3_IV: [u32; 8] = [
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
    0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
];

// ─── Rows per compression ────────────────────────────────────────────────────

pub const ROWS_PER_COMPRESSION: usize = 14; // 2 half-rounds × 7 rounds
pub const ROUNDS_PER_COMPRESSION: usize = 7;

// ─── Column groups ───────────────────────────────────────────────────────────

/// State columns: 16 words × 2 limbs = 32 columns.
/// These are DOWN columns — they flow from row N to row N+1.
pub const N_STATE_COLS: usize = 32;
pub const COL_STATE_START: ColIndex = 0;

/// Per G-function column offsets (relative to G-function start).
/// Each G-function has 8 operations (4 adds + 4 XOR-rots).
/// Columns store byte decompositions for additions and XOR results.
pub const G_ADD1_BYTES: usize = 0;     // 4 cols: a' = a + b + mx
pub const G_D_BYTES: usize = 4;        // 4 cols: byte decomp of d (for XOR step 2)
pub const G_XOR2_BYTES: usize = 8;     // 4 cols: d ^ a' result bytes
pub const G_XOR2_ADDRS: usize = 12;    // 4 cols: XOR lookup addresses
pub const G_ADD2_BYTES: usize = 16;    // 4 cols: c' = c + d'
pub const G_B_BYTES: usize = 20;       // 4 cols: byte decomp of b (for XOR step 4)
pub const G_XOR4_BYTES: usize = 24;    // 4 cols: b ^ c' result bytes
pub const G_XOR4_ADDRS: usize = 28;    // 4 cols: XOR lookup addresses
pub const G_XOR4_SPLIT: usize = 32;    // 2 cols: nibble split for >>>12
pub const G_ADD3_BYTES: usize = 34;    // 4 cols: a'' = a' + b' + my
pub const G_XOR6_BYTES: usize = 38;    // 4 cols: d' ^ a'' result bytes
pub const G_XOR6_ADDRS: usize = 42;    // 4 cols: XOR lookup addresses
pub const G_ADD4_BYTES: usize = 46;    // 4 cols: c'' = c' + d''
pub const G_XOR8_BYTES: usize = 50;    // 4 cols: b' ^ c'' result bytes
pub const G_XOR8_ADDRS: usize = 54;    // 4 cols: XOR lookup addresses
pub const G_XOR8_SPLIT: usize = 58;    // 2 cols: bit split for >>>7
pub const G_MX_VALUE: usize = 60;      // 1 col: message word mx (field element from memory)
pub const G_MX_BYTES: usize = 61;      // 4 cols: byte decomp of mx
pub const G_MX_ADDR: usize = 65;       // 1 col: memory address for mx
pub const G_MY_VALUE: usize = 66;      // 1 col: message word my (field element from memory)
pub const G_MY_BYTES: usize = 67;      // 4 cols: byte decomp of my
pub const G_MY_ADDR: usize = 71;       // 1 col: memory address for my

/// Total columns per G-function.
pub const COLS_PER_G: usize = 72;

/// G-function region: 4 G-functions after the state columns.
pub const COL_G_START: ColIndex = COL_STATE_START + N_STATE_COLS;
pub const N_G_COLS: usize = 4 * COLS_PER_G; // = 288

/// Output state columns: 16 words × 2 limbs = 32 columns.
/// These store the state AFTER the 4 G-functions have been applied.
/// The DOWN constraint links: next_row.state[w] == this_row.output_state[w].
pub const COL_OUTPUT_STATE_START: ColIndex = COL_G_START + N_G_COLS;
pub const N_OUTPUT_STATE_COLS: usize = 32;

/// Control columns (after output state).
pub const COL_CTRL_START: ColIndex = COL_OUTPUT_STATE_START + N_OUTPUT_STATE_COLS;
pub const COL_FLAG_ACTIVE: ColIndex = COL_CTRL_START;
pub const COL_IS_FIRST_ROW: ColIndex = COL_CTRL_START + 1;
pub const COL_IS_LAST_ROW: ColIndex = COL_CTRL_START + 2;
pub const COL_IS_COLUMN_QR: ColIndex = COL_CTRL_START + 3;
pub const COL_LEFT_ADDR: ColIndex = COL_CTRL_START + 4;   // down column: left input address
pub const COL_RIGHT_ADDR: ColIndex = COL_CTRL_START + 5;  // down column: right input address
pub const COL_RESULT_ADDR: ColIndex = COL_CTRL_START + 6;  // down column: output address
pub const N_CTRL_COLS: usize = 7;

/// Total committed columns.
pub const N_COMMITTED_COLS: usize = COL_CTRL_START + N_CTRL_COLS; // 32 + 288 + 32 + 7 = 359

/// Virtual columns (not committed, used for bus interaction).
pub const COL_V_INDEX_LEFT: ColIndex = N_COMMITTED_COLS;
pub const COL_V_PRECOMPILE_DATA: ColIndex = N_COMMITTED_COLS + 1;
pub const N_TOTAL_COLS: usize = N_COMMITTED_COLS + 2;

// ─── Helpers ─────────────────────────────────────────────────────────────────

/// Get the column index for the start of G-function `g` (0..3) within a row.
pub const fn g_col(g: usize, offset: usize) -> ColIndex {
    COL_G_START + g * COLS_PER_G + offset
}

/// Get the state column index for word `w` (0..15), limb `l` (0=lo, 1=hi).
pub const fn state_col(word: usize, limb: usize) -> ColIndex {
    COL_STATE_START + word * 2 + limb
}

/// Column QR G-function state word indices: G_i operates on (v[i], v[i+4], v[i+8], v[i+12]).
pub const fn col_qr_indices(g: usize) -> (usize, usize, usize, usize) {
    (g, g + 4, g + 8, g + 12)
}

/// Diagonal QR G-function state word indices: G_i operates on
/// (v[i], v[(i+1)%4 + 4], v[(i+2)%4 + 8], v[(i+3)%4 + 12]).
pub const fn diag_qr_indices(g: usize) -> (usize, usize, usize, usize) {
    (g, (g + 1) % 4 + 4, (g + 2) % 4 + 8, (g + 3) % 4 + 12)
}

// ─── Compile-time verification ───────────────────────────────────────────────

/// Get the output state column index for word `w` (0..15), limb `l` (0=lo, 1=hi).
pub const fn output_state_col(word: usize, limb: usize) -> ColIndex {
    COL_OUTPUT_STATE_START + word * 2 + limb
}

/// Down column indices: state (input) + I/O addresses.
/// The down constraint links: next_row.state == this_row.output_state.
pub fn down_columns() -> Vec<usize> {
    let mut downs = Vec::new();
    // State columns flow to next row
    for w in 0..16 {
        downs.push(state_col(w, 0));
        downs.push(state_col(w, 1));
    }
    // I/O addresses persist across rows
    downs.push(COL_LEFT_ADDR);
    downs.push(COL_RIGHT_ADDR);
    downs.push(COL_RESULT_ADDR);
    downs
}

const _: () = {
    assert!(COLS_PER_G == 72);
    assert!(N_G_COLS == 288);
    assert!(N_OUTPUT_STATE_COLS == 32);
    assert!(N_COMMITTED_COLS == 359);
    assert!(N_TOTAL_COLS == 361);
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_column_layout() {
        println!("Columns per G-function: {COLS_PER_G}");
        println!("Total G columns (4 G): {N_G_COLS}");
        println!("Total committed columns: {N_COMMITTED_COLS}");
        println!("Total columns (with virtual): {N_TOTAL_COLS}");
        println!();

        let cells_per_compression = N_COMMITTED_COLS * ROWS_PER_COMPRESSION;
        println!("Cells per compression: {cells_per_compression}");

        let n_compressions = 1060;
        let rows = n_compressions * ROWS_PER_COMPRESSION;
        let padded_rows = rows.next_power_of_two();
        let total_cells = N_COMMITTED_COLS * padded_rows;
        println!("For {n_compressions} compressions: {rows} rows (padded {padded_rows})");
        println!("Total cells: {total_cells}");
        println!("Headroom usage: {:.1}%", total_cells as f64 / 9_265_152.0 * 100.0);

        assert!(total_cells < 9_265_152, "Must fit in n_vars=26 headroom");
    }

    #[test]
    fn test_qr_indices() {
        // Column QR: straight
        assert_eq!(col_qr_indices(0), (0, 4, 8, 12));
        assert_eq!(col_qr_indices(1), (1, 5, 9, 13));
        assert_eq!(col_qr_indices(2), (2, 6, 10, 14));
        assert_eq!(col_qr_indices(3), (3, 7, 11, 15));

        // Diagonal QR: rotated
        assert_eq!(diag_qr_indices(0), (0, 5, 10, 15));
        assert_eq!(diag_qr_indices(1), (1, 6, 11, 12));
        assert_eq!(diag_qr_indices(2), (2, 7, 8, 13));
        assert_eq!(diag_qr_indices(3), (3, 4, 9, 14));
    }
}
