import ExplainableCrypto.Helios.Computational.PrimeGroup
import ExplainableCrypto.Helios.Computational.AdaptiveBallotSimulation

/-! Independent integer fixtures reduced against the original ballot simulation.
The nonzero vote distinguishes beta from alpha; distinct g/pk distinguish bases.
These controls do not invoke the general second-coordinate algebra theorem. -/

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitSecondSourceControls
instance : Fact (Nat.Prime 11) := ⟨by decide⟩
private def g : PrimeGroup 23 11 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (2 : ZMod 23) (by decide : (2 : ZMod 23)^11 = 1))
private def pk : PrimeGroup 23 11 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (4 : ZMod 23) (by decide : (4 : ZMod 23)^11 = 1))
private def stmt := honestProofStatement g pk (true,(1 : ZMod 11))

theorem honest_nonzero_vote_coordinates :
    (primeGroupCoordinate stmt.ciphertext.1).val = 2 ∧
    (primeGroupCoordinate stmt.ciphertext.2).val = 8 := by decide +kernel

theorem second_nonzero_scalar_literal :
    (primeGroupCoordinate (ballotSimCommit stmt (7 : ZMod 11) (3,5,9)).1.2).val = 2 := by
  decide +kernel

theorem generator_substitution_counterexample :
    (primeGroupCoordinate (ballotSimCommit stmt (7 : ZMod 11) (3,5,9)).1.2).val ≠
      ((2^5%23)*(8^8%23))%23 := by decide +kernel

theorem alpha_substitution_counterexample :
    (primeGroupCoordinate (ballotSimCommit stmt (7 : ZMod 11) (3,5,9)).1.2).val ≠
      ((4^5%23)*(2^8%23))%23 := by decide +kernel

theorem positive_exponent_counterexample :
    (primeGroupCoordinate (ballotSimCommit stmt (7 : ZMod 11) (3,5,9)).1.2).val ≠
      ((4^5%23)*(8^3%23))%23 := by decide +kernel

theorem second_zero_scalar_literal :
    (primeGroupCoordinate (ballotSimCommit stmt (7 : ZMod 11) (0,5,9)).1.2).val = 12 ∧
      11-(0 : ZMod 11).val = 11 ∧ (-(0 : ZMod 11)).val = 0 := by decide +kernel

theorem second_zero_response_literal :
    (primeGroupCoordinate (ballotSimCommit stmt (7 : ZMod 11) (10,0,9)).1.2).val = 8 := by
  decide +kernel

#print axioms honest_nonzero_vote_coordinates
#print axioms second_nonzero_scalar_literal
#print axioms generator_substitution_counterexample
#print axioms alpha_substitution_counterexample
#print axioms positive_exponent_counterexample
#print axioms second_zero_scalar_literal
#print axioms second_zero_response_literal
end ExplainableCrypto.Helios.Computational.PrimeSimCommitSecondSourceControls
