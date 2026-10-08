import ExplainableCrypto.Helios.Computational.PrimeGroup
import ExplainableCrypto.Helios.Computational.AdaptiveBallotSimulation

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitOneSourceControls
instance : Fact (Nat.Prime 11) := ⟨by decide⟩
private def g : PrimeGroup 23 11 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (2 : ZMod 23) (by decide : (2 : ZMod 23)^11 = 1))
private def pk : PrimeGroup 23 11 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (4 : ZMod 23) (by decide : (4 : ZMod 23)^11 = 1))
private def stmt (vote : Bool) := honestProofStatement g pk (vote,(1 : ZMod 11))

theorem vote_one_coordinates :
    (primeGroupCoordinate (ballotSimCommit (stmt true) (7 : ZMod 11) (3,5,9)).2.1).val = 9 ∧
    (primeGroupCoordinate (ballotSimCommit (stmt true) (7 : ZMod 11) (3,5,9)).2.2).val = 12 := by
  decide +kernel

theorem vote_zero_coordinates :
    (primeGroupCoordinate (ballotSimCommit (stmt false) (7 : ZMod 11) (3,5,9)).2.1).val = 9 ∧
    (primeGroupCoordinate (ballotSimCommit (stmt false) (7 : ZMod 11) (3,5,9)).2.2).val = 8 := by
  decide +kernel

theorem challenge_reuse_counterexample :
    (primeGroupCoordinate (ballotSimCommit (stmt true) (7 : ZMod 11) (3,5,9)).2.1).val ≠
      ((2^9%23)*(2^8%23))%23 := by decide +kernel

theorem unadjusted_beta_counterexample :
    (primeGroupCoordinate (ballotSimCommit (stmt true) (7 : ZMod 11) (3,5,9)).2.2).val ≠
      ((4^9%23)*(8^7%23))%23 := by decide +kernel

theorem modular_difference_underflow :
    ((2 : ZMod 11)-7).val = 6 ∧ ((2 : ZMod 11)-7).val ≠ (2-7 : Nat) ∧
    (primeGroupCoordinate (ballotSimCommit (stmt true) (2 : ZMod 11) (7,9,5)).2.1).val = 12 ∧
    (primeGroupCoordinate (ballotSimCommit (stmt true) (2 : ZMod 11) (7,9,5)).2.2).val = 6 := by
  decide +kernel

theorem zero_difference_complement :
    ((3 : ZMod 11)-3).val = 0 ∧ 11-((3 : ZMod 11)-3).val = 11 ∧
    (primeGroupCoordinate (ballotSimCommit (stmt true) (3 : ZMod 11) (3,9,5)).2.1).val = 9 ∧
    (primeGroupCoordinate (ballotSimCommit (stmt true) (3 : ZMod 11) (3,9,5)).2.2).val = 12 := by
  decide +kernel

#print axioms vote_one_coordinates
#print axioms vote_zero_coordinates
#print axioms challenge_reuse_counterexample
#print axioms unadjusted_beta_counterexample
#print axioms modular_difference_underflow
#print axioms zero_difference_complement
end ExplainableCrypto.Helios.Computational.PrimeSimCommitOneSourceControls
