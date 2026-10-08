import ExplainableCrypto.Helios.Symbolic.CiphertextCombinations
import ExplainableCrypto.Helios.Symbolic.StaticEquivalenceSPOT

namespace ExplainableCrypto.Helios.Symbolic.CiphertextCombinationSPOT
open Historical
abbrev names : Names 1 := HistoricalFrameSPOT.names
abbrev left : CandidateSubstitution 1 Empty := GeneralCandidateSPOT.selected
abbrev right : CandidateSubstitution 1 Empty := GeneralCandidateSPOT.abstain
abbrev a : General.HonestIndex 1 := (0, 1)
abbrev b : General.HonestIndex 1 := (1, 0)
abbrev c : General.HonestIndex 1 := (0, 0)
abbrev repeated : Combination (General.HonestIndex 1) :=
  .mul (.mul (.leaf a) (.leaf b)) (.mul (.leaf a) (.leaf c))
abbrev rearranged : Combination (General.HonestIndex 1) :=
  .mul (.leaf c) (.mul (.leaf a) (.mul (.leaf b) (.leaf a)))
abbrev dropped : Combination (General.HonestIndex 1) := .mul (.mul (.leaf a) (.leaf b)) (.leaf c)

/-- The public recipe equality covers reassociation, permutation and repetition. -/
theorem rearranged_products_equal (swap : Bool) :
    (General.combinationRecipe repeated).Public names.restricted ∧
    EqE ((General.frame names swap left right).eval (General.combinationRecipe repeated))
      ((General.frame names swap left right).eval (General.combinationRecipe rearranged)) := by
  refine ⟨General.combinationRecipe_public _ _, ?_⟩
  exact (General.combination_equality_iff_indices names HistoricalFrameSPOT.fixture_names_fresh
    swap left right repeated rearranged).mpr (by decide)

theorem dropping_repetition_changes_value (swap : Bool) :
    ¬ EqE ((General.frame names swap left right).eval (General.combinationRecipe repeated))
      ((General.frame names swap left right).eval (General.combinationRecipe dropped)) := by
  intro he
  have hi := (General.combination_equality_iff_indices names HistoricalFrameSPOT.fixture_names_fresh
    swap left right repeated dropped).mp he
  have hc := congrArg Multiset.card hi
  change 4 = 3 at hc
  omega

/-- The same set of indices cannot replace the exact occurrence multiset. -/
theorem sets_lose_multiplicity : repeated.indices.toFinset = dropped.indices.toFinset ∧
    repeated.indices ≠ dropped.indices := by decide

/-- The equality test is invariant even when the hidden numeric message changes
from two to zero. No equality of hidden tally values is used in the proof. -/
theorem hidden_messages_differ :
    ¬ EqE (General.combinationMessage false left right repeated)
      (General.combinationMessage true left right repeated) := by
  intro he
  have hn := he.denote (fun _ => 0) (fun _ => 0)
  change 2 = 0 at hn
  omega

theorem exact_nonce_multiplicity :
    (General.combinationNonce names repeated).composeFactors =
      { (Term.name (V := Empty) 21).baseClass, (Term.name 22).baseClass,
        (Term.name 21).baseClass, (Term.name 20).baseClass } := by
  simp [General.combinationNonce, Combination.evaluate,
    Term.composeFactors, names, HistoricalFrameSPOT.names]
  exact Multiset.cons_swap _ _ _

/-- Without injective nonce names, distinct honest index bags can have equal
ciphertext values. This is independent of the finite refutation harness. -/
theorem nonce_collision_loses_provenance :
    let ns := StaticEquivalenceSPOT.collisionNames
    let z := StaticEquivalenceSPOT.zeroVote
    let x : Combination (General.HonestIndex 1) := .leaf (0, 0)
    let y : Combination (General.HonestIndex 1) := .leaf (0, 1)
    x.indices ≠ y.indices ∧
      EqE ((General.frame ns false z z).eval (General.combinationRecipe x))
        ((General.frame ns false z z).eval (General.combinationRecipe y)) := by
  dsimp only
  refine ⟨by decide, ?_⟩
  exact (General.combination_value StaticEquivalenceSPOT.collisionNames false StaticEquivalenceSPOT.zeroVote
    StaticEquivalenceSPOT.zeroVote (.leaf (0, 0))).trans
    (General.combination_value StaticEquivalenceSPOT.collisionNames false StaticEquivalenceSPOT.zeroVote
      StaticEquivalenceSPOT.zeroVote (.leaf (0, 1))).symm

theorem offset_comparison_with_changed_hidden_sum (p q : Ground) :
    ¬ EqE (General.combinationMessage false left right repeated)
      (General.combinationMessage true left right repeated) ∧
    (EqE (.binary .add p (General.combinationMessage false left right repeated))
      (.binary .add q (General.combinationMessage false left right repeated)) ↔
    EqE (.binary .add p (General.combinationMessage true left right repeated))
      (.binary .add q (General.combinationMessage true left right repeated))) :=
  ⟨hidden_messages_differ, General.combination_offset_equality_swap left right repeated p q⟩

end ExplainableCrypto.Helios.Symbolic.CiphertextCombinationSPOT
