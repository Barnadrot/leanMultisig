use backend::*;

pub type VarCount = usize;

pub fn build_prover_state() -> ProverState<QuinticExtensionFieldKB, Blake3Permutation> {
    ProverState::new(Blake3Permutation)
}

pub fn build_verifier_state(
    prover_state: ProverState<QuinticExtensionFieldKB, Blake3Permutation>,
) -> Result<VerifierState<QuinticExtensionFieldKB, Blake3Permutation>, ProofError> {
    VerifierState::new(prover_state.into_proof(), Blake3Permutation)
}

pub trait ToUsize {
    fn to_usize(self) -> usize;
}

impl<F: PrimeField64> ToUsize for F {
    fn to_usize(self) -> usize {
        self.as_canonical_u64() as usize
    }
}
