use crate::execution::memory::MemoryAccess;
use crate::{EF, F, InstructionContext, PrecompileCompTimeArgs, RunnerError, Table};
use backend::*;

use std::{any::TypeId, cmp::Reverse, collections::BTreeMap, mem::transmute};
use utils::VarCount;

pub type ColIndex = usize;

/// Each entry: (point, eval, eval at 'shifted-down' column).
pub type CommittedStatements =
    BTreeMap<Table, Vec<(MultilinearPoint<EF>, BTreeMap<ColIndex, EF>, BTreeMap<ColIndex, EF>)>>;

/// Computed address for XOR-style lookups: address = base + hi_coeff * col[hi_col] + col[lo_col]
/// Eliminates the need for dedicated address columns.
#[derive(Debug, Clone)]
pub struct ComputedAddress {
    pub base: usize,
    pub hi_col: ColIndex,
    pub hi_coeff: usize,
    pub lo_col: ColIndex,
}

#[derive(Debug)]
pub struct LookupIntoMemory {
    pub index: ColIndex, // should be in base field columns (ignored when computed_address is Some)
    /// For (i, col_index) in values.iter().enumerate(), For j in 0..num_rows, columns_f[col_index][j] = memory[index[j] + address_offset + i]
    pub values: Vec<ColIndex>,
    /// Constant offset added to the index address (default 0).
    pub address_offset: usize,
    /// Columns whose value=1 makes the lookup inactive (numerator=0).
    /// Lookup is active when ALL listed columns are 0. Empty = always active.
    pub conditional_inactive: Vec<ColIndex>,
    /// If set, the lookup address is computed algebraically instead of read from a column.
    /// address = base + hi_coeff * col[hi_col] + col[lo_col]
    /// When Some, the `index` field is ignored.
    pub computed_address: Option<ComputedAddress>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BusDirection {
    Pull,
    Push,
}

impl BusDirection {
    pub fn to_field_flag(self) -> F {
        match self {
            BusDirection::Pull => F::NEG_ONE,
            BusDirection::Push => F::ONE,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum BusData {
    Column(ColIndex),
    ColumnPlusConstant(ColIndex, usize),
    Constant(usize),
}

impl BusData {
    pub fn column(self) -> Option<ColIndex> {
        match self {
            Self::Column(c) | Self::ColumnPlusConstant(c, _) => Some(c),
            Self::Constant(_) => None,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum BusMultiplicity {
    One,
    Column(ColIndex),
}

#[derive(Debug)]
pub struct BusInteraction {
    pub direction: BusDirection,
    pub multiplicity: BusMultiplicity,
    pub domainsep: BusData,
    pub data: Vec<BusData>,
}

impl BusInteraction {
    pub fn is_memory_lookup(&self) -> bool {
        matches!(self.domainsep, BusData::Constant(crate::LOGUP_MEMORY_DOMAINSEP))
    }
}

pub fn memory_lookups_consecutive(idx_col: ColIndex, values_start: ColIndex, n: usize) -> Vec<BusInteraction> {
    (0..n)
        .map(|i| BusInteraction {
            direction: BusDirection::Push,
            multiplicity: BusMultiplicity::One,
            domainsep: BusData::Constant(crate::LOGUP_MEMORY_DOMAINSEP),
            data: vec![
                BusData::ColumnPlusConstant(idx_col, i),
                BusData::Column(values_start + i),
            ],
        })
        .collect()
}

#[derive(Debug)]
pub struct Bus {
    pub direction: BusDirection,
    pub selector: ColIndex,
    pub data: Vec<BusData>,
}

#[derive(Debug, Default)]
pub struct TableTrace {
    pub columns: Vec<Vec<F>>,
    pub non_padded_n_rows: usize,
    pub log_n_rows: VarCount,
}

impl TableTrace {
    pub fn new<A: TableT>(air: &A) -> Self {
        Self {
            columns: vec![Vec::new(); air.n_columns_total()],
            non_padded_n_rows: 0, // filled later
            log_n_rows: 0,        // filled later
        }
    }
}

pub fn sort_tables_by_height(tables_log_heights: &BTreeMap<Table, usize>) -> Vec<(Table, usize)> {
    let mut tables_heights_sorted = tables_log_heights.clone().into_iter().collect::<Vec<_>>();
    tables_heights_sorted.sort_by_key(|&(_, h)| Reverse(h));
    tables_heights_sorted
}

#[derive(Debug, Default)]
pub struct ExtraDataForBuses<EF: ExtensionField<PF<EF>>> {
    // GKR quotient challenges
    pub logup_alphas_eq_poly: Vec<EF>,
    pub logup_alphas_eq_poly_packed: Vec<EFPacking<EF>>,
    pub bus_beta: EF,
    pub bus_beta_packed: EFPacking<EF>,
    pub alpha_powers: Vec<EF>,
}
impl<EF: ExtensionField<PF<EF>>> ExtraDataForBuses<EF> {
    pub fn new(logup_alphas_eq_poly: Vec<EF>, bus_beta: EF, alpha_powers: Vec<EF>) -> Self {
        let logup_alphas_eq_poly_packed = logup_alphas_eq_poly.iter().map(|a| EFPacking::<EF>::from(*a)).collect();
        Self {
            logup_alphas_eq_poly,
            logup_alphas_eq_poly_packed,
            bus_beta,
            bus_beta_packed: EFPacking::<EF>::from(bus_beta),
            alpha_powers,
        }
    }
}

impl AlphaPowersMut<EF> for ExtraDataForBuses<EF> {
    fn alpha_powers_mut(&mut self) -> &mut Vec<EF> {
        &mut self.alpha_powers
    }
}

impl AlphaPowers<EF> for ExtraDataForBuses<EF> {
    fn alpha_powers(&self) -> &[EF] {
        &self.alpha_powers
    }
}

impl<EF: ExtensionField<PF<EF>>> ExtraDataForBuses<EF> {
    pub fn transmute_bus_data<NewEF: 'static>(&self) -> (&Vec<NewEF>, &NewEF) {
        if TypeId::of::<NewEF>() == TypeId::of::<EF>() {
            unsafe { transmute::<(&Vec<EF>, &EF), (&Vec<NewEF>, &NewEF)>((&self.logup_alphas_eq_poly, &self.bus_beta)) }
        } else {
            assert_eq!(TypeId::of::<NewEF>(), TypeId::of::<EFPacking<EF>>());
            unsafe {
                transmute::<(&Vec<EFPacking<EF>>, &EFPacking<EF>), (&Vec<NewEF>, &NewEF)>((
                    &self.logup_alphas_eq_poly_packed,
                    &self.bus_beta_packed,
                ))
            }
        }
    }
}

/// Convention: The "AIR" columns are at the start (both for base and extension columns).
/// (Some columns may not appear in the AIR)
pub trait TableT: Air {
    fn name(&self) -> &'static str;
    fn table(&self) -> Table;
    fn lookups(&self) -> Vec<LookupIntoMemory>;
    fn bus(&self) -> Bus;
    fn bus_interactions(&self) -> Vec<BusInteraction> {
        // Default: convert from old lookups() + bus() API
        let bus = self.bus();
        let mut interactions = vec![BusInteraction {
            direction: bus.direction,
            multiplicity: BusMultiplicity::Column(bus.selector),
            domainsep: bus.data.last().copied().unwrap_or(BusData::Constant(0)),
            data: bus.data[..bus.data.len().saturating_sub(1)].to_vec(),
        }];
        for lookup in self.lookups() {
            if let Some(ca) = lookup.computed_address {
                for (i, &val_col) in lookup.values.iter().enumerate() {
                    interactions.push(BusInteraction {
                        direction: BusDirection::Push,
                        multiplicity: BusMultiplicity::One,
                        domainsep: BusData::Constant(crate::LOGUP_MEMORY_DOMAINSEP),
                        data: vec![
                            // addr = base + hi_coeff*hi_col + lo_col + address_offset + i
                            // This can't be expressed cleanly in BusData, so we skip ComputedAddress lookups
                            // in the default impl. Tables with ComputedAddress should override bus_interactions().
                            BusData::Column(val_col),
                        ],
                    });
                }
            } else {
                for (i, &val_col) in lookup.values.iter().enumerate() {
                    interactions.push(BusInteraction {
                        direction: BusDirection::Push,
                        multiplicity: BusMultiplicity::One,
                        domainsep: BusData::Constant(crate::LOGUP_MEMORY_DOMAINSEP),
                        data: vec![
                            BusData::ColumnPlusConstant(lookup.index, lookup.address_offset + i),
                            BusData::Column(val_col),
                        ],
                    });
                }
            }
        }
        interactions
    }
    fn padding_row(&self, zero_vec_ptr: usize, null_hash_ptr: usize, null_blake3_hash_ptr: usize) -> Vec<F>;
    fn execute<M: MemoryAccess>(
        &self,
        arg_a: F,
        arg_b: F,
        arg_c: F,
        args: PrecompileCompTimeArgs<usize>,
        ctx: &mut InstructionContext<'_, M>,
    ) -> Result<(), RunnerError>;

    // number of columns committed + potentially some virtual columns (useful to keep in memory for logup)
    fn n_columns_total(&self) -> usize {
        self.n_columns()
    }

    fn is_execution_table(&self) -> bool {
        false
    }

    fn lookup_index_columns<'a>(&'a self, trace: &'a TableTrace) -> Vec<&'a [F]> {
        self.lookups()
            .iter()
            .map(|lookup| &trace.columns[lookup.index][..])
            .collect()
    }
    fn lookup_value_columns<'a>(&self, trace: &'a TableTrace) -> Vec<Vec<&'a [F]>> {
        let mut cols = Vec::new();
        for lookup in self.lookups() {
            cols.push(lookup.values.iter().map(|&c| &trace.columns[c][..]).collect());
        }
        cols
    }
    fn lookup_address_offsets(&self) -> Vec<usize> {
        self.lookups().iter().map(|l| l.address_offset).collect()
    }
    fn lookup_conditional_inactive_columns<'a>(&self, trace: &'a TableTrace) -> Vec<Vec<&'a [F]>> {
        self.lookups()
            .iter()
            .map(|l| l.conditional_inactive.iter().map(|&col| &trace.columns[col][..]).collect())
            .collect()
    }
}
