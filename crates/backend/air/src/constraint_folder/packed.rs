use crate::*;
use field::*;
use poly::*;

#[derive(Debug)]
pub struct ConstraintFolderPacked<'a, IF, EF: ExtensionField<PF<EF>>, ExtraData: AlphaPowers<EF>> {
    pub up: &'a [IF],
    pub down: &'a [IF],
    pub extra_data: &'a ExtraData,
    pub accumulator: EFPacking<EF>,
    pub constraint_index: usize,
    pub skip_low: bool,
    pub accumulator_low: EFPacking<EF>,
    pub cached_state: Vec<IF>,
    pub mid_capture: Vec<IF>,
    pub mid_source: Vec<IF>,
    pub mid_offset: usize,
}

impl<'a, IF, EF, ExtraData> AirBuilder for ConstraintFolderPacked<'a, IF, EF, ExtraData>
where
    IF: Algebra<PFPacking<EF>> + 'static,
    EF: Field + ExtensionField<PF<EF>>,
    EFPacking<EF>: PrimeCharacteristicRing + Mul<IF, Output = EFPacking<EF>> + Add<IF, Output = EFPacking<EF>>,
    ExtraData: AlphaPowers<EF>,
{
    type F = PFPacking<EF>;
    type IF = IF;
    type EF = EFPacking<EF>;

    #[inline]
    fn up(&self) -> &[Self::IF] {
        self.up
    }

    #[inline]
    fn down(&self) -> &[Self::IF] {
        self.down
    }

    #[inline]
    fn assert_zero(&mut self, x: IF) {
        let alpha_power = self.extra_data.alpha_powers()[self.constraint_index];
        self.accumulator += EFPacking::<EF>::from(alpha_power) * x;
        self.constraint_index += 1;
    }

    #[inline]
    fn assert_zero_ef(&mut self, x: EFPacking<EF>) {
        let alpha_power = self.extra_data.alpha_powers()[self.constraint_index];
        self.accumulator += EFPacking::<EF>::from(alpha_power) * x;
        self.constraint_index += 1;
    }

    #[inline]
    fn assert_eq_low(&mut self, x: IF, y: IF) {
        if self.skip_low {
            self.constraint_index += 1;
            return;
        }
        let alpha_power = self.extra_data.alpha_powers()[self.constraint_index];
        let contrib = EFPacking::<EF>::from(alpha_power) * (x - y);
        self.accumulator += contrib;
        self.accumulator_low += contrib;
        self.constraint_index += 1;
    }

    #[inline]
    fn is_skip_low(&self) -> bool {
        self.skip_low
    }

    #[inline]
    fn store_cached_state(&mut self, state: &[IF]) {
        if self.cached_state.capacity() > 0 {
            self.cached_state.clear();
            self.cached_state.extend_from_slice(state);
        }
    }

    #[inline]
    fn get_cached_state(&self) -> &[IF] {
        &self.cached_state
    }

    #[inline]
    fn eval_virtual_column(&mut self, x: Self::EF) {
        self.assert_zero_ef(x);
    }

    #[inline]
    fn push_mid_state(&mut self, state: &[IF]) {
        self.mid_capture.extend_from_slice(state);
    }

    #[inline]
    fn pop_mid_state(&mut self, n: usize) -> &[IF] {
        let start = self.mid_offset;
        let end = (start + n).min(self.mid_source.len());
        self.mid_offset = end;
        &self.mid_source[start..end]
    }

    #[inline]
    fn has_mid_states(&self) -> bool {
        self.mid_offset < self.mid_source.len()
    }
}
