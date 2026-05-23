use backend::*;
use lean_vm::{
    ALL_TABLES, COL_PC, CommittedStatements, ENDING_PC, MIN_LOG_MEMORY_SIZE, MIN_LOG_N_ROWS_PER_TABLE,
    N_INSTRUCTION_COLUMNS, STARTING_PC, sort_tables_by_height,
};
use lean_vm::{EF, F, Table, TableT, TableTrace};
use std::collections::BTreeMap;
use tracing::{info_span, instrument};
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
    let total_len = 1 << stacked_n_vars;
    let mut global_polynomial: Vec<F> = unsafe { uninitialized_vec(total_len) };
    global_polynomial[..memory.len()].copy_from_slice(memory);
    let mut offset = memory.len();
    global_polynomial[offset..][..memory_acc.len()].copy_from_slice(memory_acc);
    offset += memory_acc.len();

    global_polynomial[offset..][..bytecode_acc.len()].copy_from_slice(bytecode_acc);
    let largest_table_height = 1 << tables_heights_sorted[0].1;
    let bytecode_slot = largest_table_height.max(bytecode_acc.len());
    if bytecode_slot > bytecode_acc.len() {
        global_polynomial[offset + bytecode_acc.len()..offset + bytecode_slot].fill(F::ZERO);
    }
    offset += bytecode_slot;

    let mut copy_tasks: Vec<(usize, usize, usize)> = Vec::new();
    for (table, log_n_rows) in &tables_heights_sorted {
        let n_rows = 1 << *log_n_rows;
        for col_index in 0..table.n_columns() {
            let col = &traces[table].columns[col_index];
            copy_tasks.push((offset, n_rows, col.as_ptr() as usize));
            offset += n_rows;
        }
    }
    assert_eq!(log2_ceil_usize(offset), stacked_n_vars);
    let tail_offset = offset;
    let actual_data_len = offset;
    let dst_base = global_polynomial.as_mut_ptr() as usize;
    let total_len = global_polynomial.len();

    let folding_factor_0 = whir_config_builder.folding_factor.at_round(0);
    let log_inv_rate = whir_config_builder.starting_log_inv_rate;
    let (dft_n_cols, dft_height, _effective_n_cols) =
        compute_dft_params(stacked_n_vars, actual_data_len, folding_factor_0, log_inv_rate, packing_width::<EF>());
    let dft_len = dft_height * dft_n_cols;
    let mut dft_buf: Vec<F> = unsafe { uninitialized_vec(dft_len) };
    let dft_base = dft_buf.as_mut_ptr() as usize;
    let block_size_src = (1usize << stacked_n_vars) / (1usize << folding_factor_0);
    let rate_expansion = 1usize << log_inv_rate;

    info_span!("stacking + DFT prep").in_scope(|| {
        copy_tasks.par_iter().for_each(|&(dst_offset, n, src_addr)| unsafe {
            std::ptr::copy_nonoverlapping(src_addr as *const F, (dst_base as *mut F).add(dst_offset), n);
            let col = dst_offset / block_size_src;
            if col < dft_n_cols {
                let row_base_src = dst_offset % block_size_src;
                let rows_to_write = n.min(block_size_src - row_base_src);
                for k in 0..rows_to_write {
                    let val = *((src_addr as *const F).add(k));
                    let src_row = row_base_src + k;
                    for rep in 0..rate_expansion {
                        let dft_row = src_row * rate_expansion + rep;
                        *((dft_base as *mut F).add(dft_row * dft_n_cols + col)) = val;
                    }
                }
            }
        });

        // Also write the non-table portions (memory, memory_acc, bytecode_acc) into DFT buf
        let sequential_data = &global_polynomial[..copy_tasks.first().map_or(tail_offset, |t| t.0)];
        (0..sequential_data.len()).into_par_iter().for_each(|pos| unsafe {
            let col = pos / block_size_src;
            if col < dft_n_cols {
                let src_row = pos % block_size_src;
                let val = *sequential_data.get_unchecked(pos);
                for rep in 0..rate_expansion {
                    let dft_row = src_row * rate_expansion + rep;
                    *((dft_base as *mut F).add(dft_row * dft_n_cols + col)) = val;
                }
            }
        });

        // Zero the tail in both stacked polynomial and DFT buf
        unsafe {
            std::ptr::write_bytes((dst_base as *mut F).add(tail_offset), 0, total_len - tail_offset);
        }
        for pos in tail_offset..total_len {
            let col = pos / block_size_src;
            if col < dft_n_cols {
                let src_row = pos % block_size_src;
                for rep in 0..rate_expansion {
                    let dft_row = src_row * rate_expansion + rep;
                    unsafe {
                        *((dft_base as *mut F).add(dft_row * dft_n_cols + col)) = F::ZERO;
                    }
                }
            }
        }
    });

    tracing::info!(
        "{}",
        format!(
            "stacked PCS data: {} = 2^{} * (1 + {:.2})",
            actual_data_len,
            stacked_n_vars - 1,
            (actual_data_len as f64) / (1 << (stacked_n_vars - 1)) as f64 - 1.0
        )
        .green()
    );

    let global_polynomial = MleOwned::Base(global_polynomial);
    let dft_matrix = DenseMatrix::new(dft_buf, dft_n_cols);

    let whir_config = WhirConfig::new(whir_config_builder, stacked_n_vars);
    let inner_witness =
        whir_config.commit_with_precomputed_dft(prover_state, &global_polynomial, actual_data_len, dft_matrix);
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
    use std::collections::BTreeSet;
    6 // memory + memory_acc + public_memory + bytecode_acc + pc_start + pc_end
     + ALL_TABLES
        .iter()
        .map(|table| {
            // AIR
            let air_count = table.n_columns() + table.n_down_columns();
            // Lookups into memory: count unique columns (index/hi/lo + values + conditionals)
            let mut logup_cols = BTreeSet::new();
            for lookup in table.lookups() {
                if let Some(ref ca) = lookup.computed_address {
                    // Computed address uses hi_col and lo_col instead of index
                    logup_cols.insert(ca.hi_col);
                    logup_cols.insert(ca.lo_col);
                } else {
                    logup_cols.insert(lookup.index);
                }
                for &v in &lookup.values {
                    logup_cols.insert(v);
                }
                for &c in &lookup.conditional_inactive {
                    logup_cols.insert(c);
                }
            }
            air_count + logup_cols.len()
        })
        .sum::<usize>()
        // bytecode lookup
        + 1 // PC
        + N_INSTRUCTION_COLUMNS
}
