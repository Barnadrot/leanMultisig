use crate::*;
use crate::execution::memory::MemoryAccess;
use backend::*;
use utils::{ToUsize, blake3_compress};

pub const BLAKE3_PRECOMPILE_DATA: usize = 7;
pub const BLAKE3_HALF_OUTPUT_SHIFT: usize = 1 << 3;
pub const BLAKE3_HARDCODED_LEFT_FLAG_SHIFT: usize = 1 << 4;
pub const BLAKE3_HARDCODED_LEFT_OFFSET_SHIFT: usize = 1 << 5;

pub const BLAKE3_NAME: &str = "blake3_compress";
pub const BLAKE3_HALF_NAME: &str = "blake3_compress_half";
pub const BLAKE3_HARDCODED_LEFT_NAME: &str = "blake3_compress_hardcoded_left";
pub const BLAKE3_HALF_HARDCODED_LEFT_NAME: &str = "blake3_compress_half_hardcoded_left";
pub const ALL_BLAKE3_NAMES: [&str; 4] = [
    BLAKE3_NAME,
    BLAKE3_HALF_NAME,
    BLAKE3_HARDCODED_LEFT_NAME,
    BLAKE3_HALF_HARDCODED_LEFT_NAME,
];

pub const BLAKE3_COL_FLAG: ColIndex = 0;
pub const BLAKE3_COL_INDEX_RIGHT: ColIndex = 1;
pub const BLAKE3_COL_INDEX_RES: ColIndex = 2;
pub const BLAKE3_COL_FLAG_HALF_OUTPUT: ColIndex = 3;
pub const BLAKE3_COL_FLAG_HARDCODED_LEFT: ColIndex = 4;
pub const BLAKE3_COL_OFFSET_HARDCODED_LEFT: ColIndex = 5;
pub const BLAKE3_COL_EFFECTIVE_INDEX_LEFT_FIRST: ColIndex = 6;
pub const BLAKE3_COL_EFFECTIVE_INDEX_LEFT_SECOND: ColIndex = 7;
pub const BLAKE3_COL_INPUT_START: ColIndex = 8;
pub const BLAKE3_COL_OUTPUT_START: ColIndex = BLAKE3_COL_INPUT_START + DIGEST_LEN * 2;
pub const BLAKE3_N_COMMITTED_COLS: usize = BLAKE3_COL_OUTPUT_START + DIGEST_LEN;
pub const BLAKE3_COL_INDEX_LEFT: ColIndex = BLAKE3_N_COMMITTED_COLS;
pub const BLAKE3_COL_PRECOMPILE_DATA: ColIndex = BLAKE3_N_COMMITTED_COLS + 1;
pub const BLAKE3_N_TOTAL_COLS: usize = BLAKE3_N_COMMITTED_COLS + 2;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Blake3CompressPrecompile<const BUS: bool>;

impl<const BUS: bool> TableT for Blake3CompressPrecompile<BUS> {
    fn name(&self) -> &'static str {
        BLAKE3_NAME
    }

    fn table(&self) -> Table {
        Table::blake3()
    }

    fn lookups(&self) -> Vec<LookupIntoMemory> {
        vec![
            LookupIntoMemory {
                index: BLAKE3_COL_EFFECTIVE_INDEX_LEFT_FIRST,
                values: (BLAKE3_COL_INPUT_START..BLAKE3_COL_INPUT_START + HALF_DIGEST_LEN).collect(),
                address_offset: 0,
                conditional_inactive: vec![],
            },
            LookupIntoMemory {
                index: BLAKE3_COL_EFFECTIVE_INDEX_LEFT_SECOND,
                values: (BLAKE3_COL_INPUT_START + HALF_DIGEST_LEN..BLAKE3_COL_INPUT_START + DIGEST_LEN).collect(),
                address_offset: 0,
                conditional_inactive: vec![],
            },
            LookupIntoMemory {
                index: BLAKE3_COL_INDEX_RIGHT,
                values: (BLAKE3_COL_INPUT_START + DIGEST_LEN..BLAKE3_COL_INPUT_START + DIGEST_LEN * 2).collect(),
                address_offset: 0,
                conditional_inactive: vec![],
            },
            LookupIntoMemory {
                index: BLAKE3_COL_INDEX_RES,
                values: (BLAKE3_COL_OUTPUT_START..BLAKE3_COL_OUTPUT_START + HALF_DIGEST_LEN).collect(),
                address_offset: 0,
                conditional_inactive: vec![],
            },
            LookupIntoMemory {
                index: BLAKE3_COL_INDEX_RES,
                values: (BLAKE3_COL_OUTPUT_START + HALF_DIGEST_LEN..BLAKE3_COL_OUTPUT_START + DIGEST_LEN).collect(),
                address_offset: HALF_DIGEST_LEN,
                conditional_inactive: vec![BLAKE3_COL_FLAG_HALF_OUTPUT],
            },
        ]
    }

    fn n_columns_total(&self) -> usize {
        BLAKE3_N_TOTAL_COLS
    }

    fn bus(&self) -> Bus {
        let mut data = Vec::with_capacity(4);
        data.push(BusData::Column(BLAKE3_COL_PRECOMPILE_DATA));
        data.push(BusData::Column(BLAKE3_COL_INDEX_LEFT));
        data.push(BusData::Column(BLAKE3_COL_INDEX_RIGHT));
        data.push(BusData::Column(BLAKE3_COL_INDEX_RES));
        Bus {
            direction: BusDirection::Pull,
            selector: BLAKE3_COL_FLAG,
            data,
        }
    }

    fn padding_row(&self, zero_vec_ptr: usize, _null_hash_ptr: usize, null_blake3_hash_ptr: usize) -> Vec<F> {
        let mut row = vec![F::ZERO; BLAKE3_N_TOTAL_COLS];
        row[BLAKE3_COL_FLAG] = F::ZERO;
        row[BLAKE3_COL_INDEX_RIGHT] = F::from_usize(zero_vec_ptr);
        row[BLAKE3_COL_INDEX_RES] = F::from_usize(null_blake3_hash_ptr);
        row[BLAKE3_COL_FLAG_HALF_OUTPUT] = F::ZERO;
        row[BLAKE3_COL_FLAG_HARDCODED_LEFT] = F::ZERO;
        row[BLAKE3_COL_OFFSET_HARDCODED_LEFT] = F::ZERO;
        row[BLAKE3_COL_EFFECTIVE_INDEX_LEFT_FIRST] = F::from_usize(zero_vec_ptr);
        row[BLAKE3_COL_EFFECTIVE_INDEX_LEFT_SECOND] = F::from_usize(zero_vec_ptr + HALF_DIGEST_LEN);
        let null_output = blake3_compress(&[F::ZERO; 8], &[F::ZERO; 8]);
        for (i, &val) in null_output.iter().enumerate() {
            row[BLAKE3_COL_OUTPUT_START + i] = val;
        }
        row[BLAKE3_COL_INDEX_LEFT] = F::from_usize(zero_vec_ptr);
        row[BLAKE3_COL_PRECOMPILE_DATA] = F::from_usize(BLAKE3_PRECOMPILE_DATA);
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
        let trace = ctx.traces.get_mut(&self.table()).unwrap();

        let arg_a_usize = arg_a.to_usize();
        let flag_hardcoded = hardcoded_offset_left.is_some();
        let left_first_addr = hardcoded_offset_left.unwrap_or(arg_a_usize);
        let left_second_addr = if flag_hardcoded {
            arg_a_usize
        } else {
            arg_a_usize + HALF_DIGEST_LEN
        };
        let arg0_first = ctx.memory.get_slice(left_first_addr, HALF_DIGEST_LEN)?;
        let arg0_second = ctx.memory.get_slice(left_second_addr, HALF_DIGEST_LEN)?;
        let right = ctx.memory.get_slice(arg_b.to_usize(), DIGEST_LEN)?;

        let mut input = [F::ZERO; DIGEST_LEN * 2];
        input[..HALF_DIGEST_LEN].copy_from_slice(&arg0_first);
        input[HALF_DIGEST_LEN..DIGEST_LEN].copy_from_slice(&arg0_second);
        input[DIGEST_LEN..].copy_from_slice(&right);

        let left_arr: &[F; 8] = input[..8].try_into().unwrap();
        let right_arr: &[F; 8] = input[8..].try_into().unwrap();
        let output = blake3_compress(left_arr, right_arr);

        let res_addr = index_res.to_usize();
        if half_output {
            ctx.memory.set_slice(res_addr, &output[..HALF_DIGEST_LEN])?;
        } else {
            ctx.memory.set_slice(res_addr, &output)?;
        }

        let hardcoded_offset_left_val = hardcoded_offset_left.unwrap_or(0);

        trace.columns[BLAKE3_COL_FLAG].push(F::ONE);
        trace.columns[BLAKE3_COL_INDEX_RIGHT].push(arg_b);
        trace.columns[BLAKE3_COL_INDEX_RES].push(index_res);
        trace.columns[BLAKE3_COL_FLAG_HALF_OUTPUT].push(F::from_bool(half_output));
        trace.columns[BLAKE3_COL_FLAG_HARDCODED_LEFT].push(F::from_bool(flag_hardcoded));
        trace.columns[BLAKE3_COL_OFFSET_HARDCODED_LEFT].push(F::from_usize(hardcoded_offset_left_val));
        trace.columns[BLAKE3_COL_EFFECTIVE_INDEX_LEFT_FIRST].push(F::from_usize(left_first_addr));
        trace.columns[BLAKE3_COL_EFFECTIVE_INDEX_LEFT_SECOND].push(F::from_usize(left_second_addr));
        for (i, &val) in input.iter().enumerate() {
            trace.columns[BLAKE3_COL_INPUT_START + i].push(val);
        }
        for (i, &val) in output.iter().enumerate() {
            trace.columns[BLAKE3_COL_OUTPUT_START + i].push(val);
        }
        // Virtual columns
        trace.columns[BLAKE3_COL_INDEX_LEFT].push(arg_a);
        let precompile_data = BLAKE3_PRECOMPILE_DATA
            + BLAKE3_HALF_OUTPUT_SHIFT * (half_output as usize)
            + BLAKE3_HARDCODED_LEFT_FLAG_SHIFT * (flag_hardcoded as usize)
            + BLAKE3_HARDCODED_LEFT_OFFSET_SHIFT * hardcoded_offset_left_val;
        trace.columns[BLAKE3_COL_PRECOMPILE_DATA].push(F::from_usize(precompile_data));

        Ok(())
    }
}

impl<const BUS: bool> Air for Blake3CompressPrecompile<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;

    fn n_columns(&self) -> usize {
        BLAKE3_N_COMMITTED_COLS
    }

    fn degree_air(&self) -> usize {
        3
    }

    fn down_column_indexes(&self) -> Vec<usize> {
        vec![]
    }

    fn n_constraints(&self) -> usize {
        BUS as usize + 5
    }

    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let flag_active = builder.up()[BLAKE3_COL_FLAG];
        let flag_half_output = builder.up()[BLAKE3_COL_FLAG_HALF_OUTPUT];
        let flag_hardcoded_left = builder.up()[BLAKE3_COL_FLAG_HARDCODED_LEFT];
        let offset_hardcoded_left = builder.up()[BLAKE3_COL_OFFSET_HARDCODED_LEFT];
        let effective_index_left_first = builder.up()[BLAKE3_COL_EFFECTIVE_INDEX_LEFT_FIRST];
        let effective_index_left_second = builder.up()[BLAKE3_COL_EFFECTIVE_INDEX_LEFT_SECOND];
        let index_right = builder.up()[BLAKE3_COL_INDEX_RIGHT];
        let index_res = builder.up()[BLAKE3_COL_INDEX_RES];

        let precompile_data_reconstructed: AB::IF =
            AB::F::from_usize(BLAKE3_PRECOMPILE_DATA).into();
        let precompile_data_reconstructed = precompile_data_reconstructed
            + flag_half_output * AB::F::from_usize(BLAKE3_HALF_OUTPUT_SHIFT)
            + flag_hardcoded_left * AB::F::from_usize(BLAKE3_HARDCODED_LEFT_FLAG_SHIFT)
            + flag_hardcoded_left
                * offset_hardcoded_left
                * AB::F::from_usize(BLAKE3_HARDCODED_LEFT_OFFSET_SHIFT);

        let one_minus_flag_hardcoded_left = AB::IF::ONE - flag_hardcoded_left;
        let index_a =
            effective_index_left_second - one_minus_flag_hardcoded_left * AB::F::from_usize(HALF_DIGEST_LEN);

        if BUS {
            builder.assert_zero_ef(eval_virtual_bus_column::<AB, EF>(
                extra_data,
                flag_active,
                &[precompile_data_reconstructed, index_a, index_right, index_res],
            ));
        } else {
            builder.declare_values(std::slice::from_ref(&flag_active));
            builder.declare_values(&[precompile_data_reconstructed, index_a, index_right, index_res]);
        }

        builder.assert_bool(flag_active);
        builder.assert_bool(flag_half_output);
        builder.assert_bool(flag_hardcoded_left);

        builder.assert_zero(flag_hardcoded_left * (offset_hardcoded_left - effective_index_left_first));
        builder.assert_zero(one_minus_flag_hardcoded_left * (index_a - effective_index_left_first));
    }
}
