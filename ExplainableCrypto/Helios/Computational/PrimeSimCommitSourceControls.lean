import ExplainableCrypto.Helios.Computational.PrimeSimCommitSource
import ExplainableCrypto.Helios.Computational.PrimeGroup
import ExplainableCrypto.Helios.Computational.BallotSigmaSimulation


namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitSourceControls
instance : Fact (Nat.Prime 11) := ⟨by decide⟩
instance : Fact (Nat.Prime 2) := ⟨by decide⟩
private def g : PrimeGroup 23 11 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (2 : ZMod 23) (by decide : (2 : ZMod 23)^11 = 1))
private def alpha : PrimeGroup 23 11 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (4 : ZMod 23) (by decide : (4 : ZMod 23)^11 = 1))
private def stmt : BallotStatement (PrimeGroup 23 11) := ⟨g,0,(alpha,0)⟩

theorem source_first_literal :
    (primeGroupCoordinate (ballotSimCommit stmt (7 : ZMod 11) (3,5,9)).1.1).val = 12 := by
  decide +kernel

theorem positive_exponent_counterexample :
    (primeGroupCoordinate (ballotSimCommit stmt (7 : ZMod 11) (3,5,9)).1.1).val ≠
      ((2^5%23)*(4^3%23))%23 := by decide +kernel

theorem wrong_challenge_counterexample :
    (primeGroupCoordinate (ballotSimCommit stmt (7 : ZMod 11) (3,5,9)).1.1).val ≠
      ((2^5%23)*(4^4%23))%23 := by decide +kernel

theorem omitted_factor_counterexample :
    (primeGroupCoordinate (ballotSimCommit stmt (7 : ZMod 11) (3,5,9)).1.1).val ≠ 2^5%23 := by
  decide +kernel

theorem canonical_zero_exponent :
    (-(0 : ZMod 11)).val = 0 ∧
    (primeGroupCoordinate (ballotSimCommit stmt (7 : ZMod 11) (0,0,9)).1.1).val = 1 := by
  decide +kernel

theorem identity_generator_allowed :
    (primeGroupCoordinate (ballotSimCommit (⟨0,0,(alpha,0)⟩ : BallotStatement (PrimeGroup 23 11))
      (7 : ZMod 11) (3,5,9)).1.1).val = 9 := by decide +kernel

private def compositeG : PrimeGroup 15 2 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (14 : ZMod 15) (by decide : (14 : ZMod 15)^2 = 1))
private def compositeAlpha : PrimeGroup 15 2 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (4 : ZMod 15) (by decide : (4 : ZMod 15)^2 = 1))

theorem composite_modulus_allowed :
    (primeGroupCoordinate (ballotSimCommit
      (⟨compositeG,0,(compositeAlpha,0)⟩ : BallotStatement (PrimeGroup 15 2))
      (0 : ZMod 2) (1,1,0)).1.1).val = 11 := by decide +kernel

/-- The executed complement keeps q at zero; it is not canonical scalar negation,
but actual subgroup membership gives the same action. -/
theorem complement_zero_same_action :
    11-(0 : ZMod 11).val = 11 ∧ (-(0 : ZMod 11)).val = 0 ∧
    (primeGroupCoordinate alpha)^(11-(0 : ZMod 11).val) =
      (primeGroupCoordinate alpha)^(-(0 : ZMod 11)).val := by decide +kernel

/-- Mere nonzero residues do not justify the complement-at-zero shortcut. -/
theorem non_subgroup_complement_counterexample :
    (5 : ZMod 23) ≠ 0 ∧ (5 : ZMod 23)^11 ≠ (5 : ZMod 23)^0 := by decide +kernel

#print axioms complement_zero_same_action
#print axioms non_subgroup_complement_counterexample
#print axioms source_first_literal
#print axioms positive_exponent_counterexample
#print axioms wrong_challenge_counterexample
#print axioms omitted_factor_counterexample
#print axioms canonical_zero_exponent
#print axioms identity_generator_allowed
#print axioms composite_modulus_allowed
end ExplainableCrypto.Helios.Computational.PrimeSimCommitSourceControls
