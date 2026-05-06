use backend::*;
use lean_vm::{
    ALL_TABLES, COL_PC, CommittedStatements, ENDING_PC, MIN_LOG_MEMORY_SIZE, MIN_LOG_N_ROWS_PER_TABLE,
    N_INSTRUCTION_COLUMNS, STARTING_PC, sort_tables_by_height,
};
use lean_vm::{EF, F, Table, TableT, TableTrace};
use std::collections::BTreeMap;
use tracing::instrument;
use utils::VarCount;
use utils::ansi::Colorize;

/*
Stacking of various (multilinear) polynomials into a single -big- (multilinear) polynomial, which is committed via WHIR.
[------------------------------ Memory ------------------------------]
[------------------------ Memory Accumulator ------------------------]
[------ Bytecode Accumulator -----]                             (padded to bas as least as large as the execution table)
[-------- Execution Col 0 --------]
[-------- Execution Col 1 --------]
...
[-------- Execution Col 19 -------]
[Dot-Product Col 0]
[Dot-Product Col 1]
...
[Dot-Product Col n]
[Poseidon-16 Col 0]
[Poseidon-16 Col 1]
...
[Poseidon-16 Col m]

(The order between Dot-Product and Poseidon-16 varies based on which table has more rows, but they are always after the execution table)
*/

#[derive(Debug)]
pub struct StackedPcsWitness {
    pub stacked_n_vars: VarCount,
    pub inner_witness: Witness<EF>,
    pub global_polynomial: MleOwned<EF>,
}

pub fn stacked_pcs_global_statements(
    stacked_n_vars: VarCount,
    memory_n_vars: VarCount,
    bytecode_n_vars: VarCount,
    previous_statements: Vec<SparseStatement<EF>>,
    tables_heights: &BTreeMap<Table, VarCount>,
    committed_statements: &CommittedStatements,
) -> Vec<SparseStatement<EF>> {
    assert_eq!(tables_heights.len(), committed_statements.len());

    let tables_heights_sorted = sort_tables_by_height(tables_heights);

    let mut global_statements = previous_statements;
    let mut offset = 2 << memory_n_vars; // memory + memory_acc

    let max_table_n_vars = tables_heights_sorted[0].1;
    offset += 1 << bytecode_n_vars.max(max_table_n_vars); // bytecode acc

    for (table, n_vars) in tables_heights_sorted {
        if table.is_execution_table() {
            // Important: ensure both initial and final PC conditions are correct
            global_statements.push(SparseStatement::unique_value(
                stacked_n_vars,
                offset + (COL_PC << n_vars),
                EF::from_usize(STARTING_PC),
            ));
            global_statements.push(SparseStatement::unique_value(
                stacked_n_vars,
                offset + ((COL_PC + 1) << n_vars) - 1,
                EF::from_usize(ENDING_PC),
            ));
        }
        for (point, eq_values, next_values) in &committed_statements[&table] {
            if !next_values.is_empty() {
                global_statements.push(SparseStatement::new_next(
                    stacked_n_vars,
                    point.clone(),
                    next_values
                        .iter()
                        .map(|(&col_index, &value)| SparseValue::new((offset >> n_vars) + col_index, value))
                        .collect(),
                ));
            }
            global_statements.push(SparseStatement::new(
                stacked_n_vars,
                point.clone(),
                eq_values
                    .iter()
                    .map(|(&col_index, &value)| SparseValue::new((offset >> n_vars) + col_index, value))
                    .collect(),
            ));
        }
        offset += table.n_columns() << n_vars;
    }
    global_statements
}

#[instrument(skip_all)]
pub fn stack_polynomials_and_commit(
    prover_state: &mut impl FSProver<EF>,
    whir_config_builder: &WhirConfigBuilder,
    memory: &[F],
    memory_acc: &[F],
    bytecode_acc: &[F],
    traces: &BTreeMap<Table, TableTrace>,
) -> StackedPcsWitness {
    assert_eq!(memory.len(), memory_acc.len());
    let tables_heights = traces.iter().map(|(table, trace)| (*table, trace.log_n_rows)).collect();
    let tables_heights_sorted = sort_tables_by_height(&tables_heights);
    assert!(log2_strict_usize(memory.len()) >= tables_heights[&Table::execution()]); // memory must be at least as large as the number of cycles (TODO add some padding when this is not the case)
    assert!(tables_heights[&Table::execution()] >= tables_heights_sorted[0].1); // execution table must be the largest table (TODO add some padding when this is not the case)

    let stacked_n_vars = compute_stacked_n_vars(
        log2_strict_usize(memory.len()),
        log2_strict_usize(bytecode_acc.len()),
        &tables_heights_sorted.iter().cloned().collect(),
    );
    let mut global_polynomial = F::zero_vec(1 << stacked_n_vars); // TODO avoid cloning all witness data

    // Build a list of (dst_offset, src_slice) copy specs. Large segments
    // (memory, memory_acc, bytecode_acc) are split into ~4 MB chunks so they
    // distribute across rayon workers rather than hogging a single thread.
    use rayon::prelude::*;
    const CHUNK_BYTES: usize = 4 * 1024 * 1024;
    let chunk_elems = CHUNK_BYTES / std::mem::size_of::<F>();
    let mut copies: Vec<(usize, &[F])> = Vec::new();
    let mut push_chunked = |copies: &mut Vec<(usize, &[F])>, base: usize, src: &'_ [F]| {
        let mut start = 0;
        while start < src.len() {
            let end = (start + chunk_elems).min(src.len());
            // SAFETY: lifetimes are bounded by the function's input borrows,
            // which outlive the par_iter below.
            let slice: &[F] = unsafe { std::slice::from_raw_parts(src.as_ptr().add(start), end - start) };
            copies.push((base + start, slice));
            start = end;
        }
    };

    let mut offset = 0usize;
    push_chunked(&mut copies, offset, memory);
    offset += memory.len();
    push_chunked(&mut copies, offset, memory_acc);
    offset += memory_acc.len();
    push_chunked(&mut copies, offset, bytecode_acc);
    let largest_table_height = 1 << tables_heights_sorted[0].1;
    offset += largest_table_height.max(bytecode_acc.len()); // pad bytecode_acc to max table height

    for (table, log_n_rows) in &tables_heights_sorted {
        let n_rows = 1 << *log_n_rows;
        for col_index in 0..table.n_columns() {
            let col = &traces[table].columns[col_index];
            copies.push((offset, &col[..n_rows]));
            offset += n_rows;
        }
    }

    // SAFETY: each (start, src) pair targets a disjoint slice of
    // global_polynomial. Concurrent writes through the raw pointer never alias.
    let dst_ptr = global_polynomial.as_mut_ptr() as usize;
    copies.par_iter().for_each(|&(start, src)| {
        let n = src.len();
        unsafe {
            let dst = (dst_ptr as *mut F).add(start);
            std::ptr::copy_nonoverlapping(src.as_ptr(), dst, n);
        }
    });
    assert_eq!(log2_ceil_usize(offset), stacked_n_vars);
    tracing::info!(
        "{}",
        format!(
            "stacked PCS data: {} = 2^{} * (1 + {:.2})",
            offset,
            stacked_n_vars - 1,
            (offset as f64) / (1 << (stacked_n_vars - 1)) as f64 - 1.0
        )
        .green()
    );

    let global_polynomial = MleOwned::Base(global_polynomial);

    let inner_witness =
        WhirConfig::new(whir_config_builder, stacked_n_vars).commit(prover_state, &global_polynomial, offset);
    StackedPcsWitness {
        stacked_n_vars,
        inner_witness,
        global_polynomial,
    }
}

pub fn stacked_pcs_parse_commitment(
    whir_config_builder: &WhirConfigBuilder,
    verifier_state: &mut impl FSVerifier<EF>,
    log_memory: usize,
    log_bytecode: usize,
    tables_heights: &BTreeMap<Table, VarCount>,
) -> Result<ParsedCommitment<F, EF>, ProofError> {
    if log_memory < tables_heights[&Table::execution()]
        || tables_heights[&Table::execution()] < tables_heights.values().copied().max().unwrap()
    {
        // memory must be at least as large as the number of cycles
        // execution table must be the largest table
        return Err(ProofError::InvalidProof);
    }

    let stacked_n_vars = compute_stacked_n_vars(log_memory, log_bytecode, tables_heights);
    if stacked_n_vars
        > F::TWO_ADICITY + whir_config_builder.folding_factor.at_round(0) - whir_config_builder.starting_log_inv_rate
    {
        return Err(ProofError::InvalidProof);
    }
    WhirConfig::new(whir_config_builder, stacked_n_vars).parse_commitment(verifier_state)
}

fn compute_stacked_n_vars(
    log_memory: usize,
    log_bytecode: usize,
    tables_log_heights: &BTreeMap<Table, VarCount>,
) -> VarCount {
    let max_table_log_n_rows = tables_log_heights.values().copied().max().unwrap();
    let total_len = (2 << log_memory)
        + (1 << log_bytecode.max(max_table_log_n_rows))
        + tables_log_heights
            .iter()
            .map(|(table, log_n_rows)| table.n_columns() << log_n_rows)
            .sum::<usize>();
    log2_ceil_usize(total_len)
}

pub fn min_stacked_n_vars(log_bytecode: usize) -> usize {
    let mut min_tables_log_heights = BTreeMap::new();
    for table in ALL_TABLES {
        min_tables_log_heights.insert(table, MIN_LOG_N_ROWS_PER_TABLE);
    }
    compute_stacked_n_vars(MIN_LOG_MEMORY_SIZE, log_bytecode, &min_tables_log_heights)
}

pub fn total_whir_statements() -> usize {
    6 // memory + memory_acc + public_memory + bytecode_acc + pc_start + pc_end
     + ALL_TABLES
        .iter()
        .map(|table| {
            // AIR
            table.n_columns()
            + table.n_down_columns()
            // Lookups into memory
            + table.lookups().iter().map(|lookup| 1 + lookup.values.len()).sum::<usize>()
        })
        .sum::<usize>()
        // bytecode lookup
        + 1 // PC
        + N_INSTRUCTION_COLUMNS
}
