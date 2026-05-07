mod normal;
pub use normal::*;

mod packed;
pub use packed::*;

use field::{ExtensionField, Field};
use poly::{EFPacking, PF};

pub trait AlphaPowers<EF> {
    fn alpha_powers(&self) -> &[EF];
}

impl<EF: Field> AlphaPowers<EF> for Vec<EF> {
    #[inline(always)]
    fn alpha_powers(&self) -> &[EF] {
        self
    }
}

/// Provides pre-broadcast packed alpha powers for the packed constraint folder,
/// so `assert_zero` can avoid an `EFPacking::from(scalar)` conversion (5
/// `vpbroadcastd` per call) on every constraint.
pub trait AlphaPowersPacked<EF: ExtensionField<PF<EF>>> {
    fn alpha_powers_packed(&self) -> &[EFPacking<EF>];
}

/// `Vec<EF>` is used as `ExtraData` only by sumcheck paths where alpha_powers
/// is asserted empty (see sc_computation.rs). Return an empty slice.
impl<EF: ExtensionField<PF<EF>>> AlphaPowersPacked<EF> for Vec<EF> {
    #[inline(always)]
    fn alpha_powers_packed(&self) -> &[EFPacking<EF>] {
        &[]
    }
}

pub trait AlphaPowersMut<EF> {
    fn alpha_powers_mut(&mut self) -> &mut Vec<EF>;
}

impl<EF: Field> AlphaPowersMut<EF> for Vec<EF> {
    #[inline(always)]
    fn alpha_powers_mut(&mut self) -> &mut Vec<EF> {
        self
    }
}
