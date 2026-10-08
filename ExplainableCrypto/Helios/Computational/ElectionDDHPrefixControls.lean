import ExplainableCrypto.Helios.Computational.ElectionDDHPrefix
import ExplainableCrypto.Helios.Computational.ElectionProgrammedExtractionControls

/-! Querying prefix controls use a non-DH challenge and the existing saved-
answer-dependent callbacks. Small-field arithmetic makes no hardness claim. -/
namespace ExplainableCrypto.Helios.Computational.ElectionDDHPrefixControls
open OracleComp OracleSpec ElectionOracle ElectionDDHSource ElectionProgrammedExtractionControls
local instance : Fact (Nat.Prime 257) := ⟨by decide +kernel⟩
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar
noncomputable local instance : IsUniformSpec ((Unit →ₒ Scalar) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

private theorem prepare_bound : prepare.IsQueryBoundP (ElectionQueryBound.isBallot (F := Scalar)) 1 := by
  simp [prepare,ask,key,ElectionQueryBound.isBallot]

private theorem cast_bound (b : Ballot Scalar Scalar 2) (remembered : Scalar × Scalar)
    (before : PublicPrefix Scalar Scalar) :
    ((adversary b remembered).castBallot before).IsQueryBoundP
      (ElectionQueryBound.isBallot (F := Scalar)) 0 := by
  simp [adversary,ask,key,ElectionQueryBound.isBallot]

/-- Preparation queries both proof domains, casting queries again, and the
actual prefix has ten live ballot-hash queries at most. -/
theorem bound_after_queries (b : Ballot Scalar Scalar 2) :
    (prefixSource (fun p => p.trusteeKeyProof.response.val) 1 3 2 7 prepare (adversary b)).IsQueryBoundP
      (isBallotHashQuery (F := Scalar)) 10 := by
  with_reducible
    exact prefix_bound (F := Scalar) (G := Scalar)
      (fun p => p.trusteeKeyProof.response.val) 1 3 2 7 prepare
      (adversary b) 1 0 prepare_bound (cast_bound b)

/-- The common-path context allowance is 33δ for this actual prefix. Its
acceptance mass remains the actual three-decision event, not an assumed one. -/
theorem joint_after_queries (b : Ballot Scalar Scalar 2) (δ : ENNReal) :
    let a := Pr[fun out => PrefixAccepted out.1 | runBallotOracle
      (prefixSource (fun p => p.trusteeKeyProof.response.val) 1 3 2 7 prepare (adversary b)) ∅]
    (a-33*δ)*(δ-1/257)^3 ≤ Pr[fun out => out.isSome |
      prefixJoint (fun p => p.trusteeKeyProof.response.val) 1 3 2 7 prepare (adversary b) 10] := by
  have h := prefix_joint_le (fun p => p.trusteeKeyProof.response.val) 1 3 2 7
    (by decide +kernel : (1 : Scalar) ≠ 0) prepare (adversary b) 1 0 prepare_bound (cast_bound b) δ
  norm_num at h ⊢
  exact h

/-- This source and bound do not require a hidden honest ciphertext witness. -/
theorem challenge_is_not_dh : (2 : Scalar) • (3 : Scalar) ≠ 7 := by decide +kernel

/-- Extraction cannot execute the guessing callback: changing that callback
leaves the complete prefix source, including its query tree, identical. -/
theorem stops_before_guess (b : Ballot Scalar Scalar 2) :
    prefixSource (fun p => p.trusteeKeyProof.response.val) 1 3 2 7 prepare
      (fun remembered => {adversary b remembered with guessVote := fun _ _ => pure true}) =
    prefixSource (fun p => p.trusteeKeyProof.response.val) 1 3 2 7 prepare (adversary b) := rfl

/-- The two guessing callbacks really differ; the preceding equality does not
follow from replacing a callback by an equivalent one. -/
theorem guessing_suffix_differs (b : Ballot Scalar Scalar 2) (remembered : Scalar × Scalar)
    (saved : Scalar) (view : PublicResult Scalar Scalar) :
    (adversary b remembered).guessVote saved view ≠ pure true := by
  have hn : ¬ ((adversary b remembered).guessVote saved view).IsQueryBoundP
      (ElectionCacheBudget.isHash (F := Scalar)) 0 := by
    simp [adversary,ask,ElectionCacheBudget.isHash]
  intro he
  rw [he] at hn
  exact hn (by simp)

private def preparationDependent (initial : Bool) (b : Ballot Scalar Scalar 2) :
    Adversary Scalar Scalar Unit :=
  ⟨fun _ => pure (b,()), fun _ _ => pure initial⟩

/-- Equal casting state need not determine the guessing callback: preparation
alone can change its result. The retained prefix therefore keeps both states. -/
theorem preparation_changes_guess (b : Ballot Scalar Scalar 2) (view : PublicResult Scalar Scalar) :
    (preparationDependent true b).guessVote () view = pure true ∧
    (preparationDependent false b).guessVote () view = pure false := ⟨rfl,rfl⟩

/-- Arithmetic nonvacuity at a=1, δ=1/200; it does not assert actual mass a=1. -/
theorem positive_bound_possible : (0 : ENNReal) < (1-33*(1/200))*(1/200-1/257)^3 := by
  have hn : (0 : NNReal) < (1-33*(1/200))*(1/200-1/257)^3 := by
    change (0 : ℝ) < ((1-33*(1/200) : NNReal)*(1/200-1/257)^3 : NNReal)
    norm_num [NNReal.coe_sub_def]
  simpa [ENNReal.coe_sub,ENNReal.coe_div] using (ENNReal.coe_lt_coe.mpr hn)

#print axioms preparation_changes_guess
#print axioms bound_after_queries
#print axioms joint_after_queries
#print axioms challenge_is_not_dh
#print axioms stops_before_guess
#print axioms guessing_suffix_differs
#print axioms positive_bound_possible
end ExplainableCrypto.Helios.Computational.ElectionDDHPrefixControls
