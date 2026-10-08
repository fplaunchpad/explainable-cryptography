import ExplainableCrypto.Helios.Symbolic.DecryptCheckMixedMulTransport

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n handles : Nat}
namespace CiphertextAssembly

/-- Count public constructor occurrences, retaining multiplicity. Honest
selectors contribute zero even when their evaluated value is a ciphertext. -/
def constructedCount : CiphertextAssembly n handles → Nat
  | .constructed _ _ _ => 1
  | .honest _ => 0
  | .mul a b => a.constructedCount+b.constructedCount

/-- Exact honest selector costs and all public component occurrences fit in
the original tree. Each additional constructed occurrence pays a fusion saving. -/
theorem group_occurrence_budget (t : CiphertextAssembly n) :
    match t.group with
    | .constructed r p => 0 < t.constructedCount ∧
        r.nodeCount+p.nodeCount+1+t.constructedCount ≤ t.recipe.nodeCount
    | .honest a => t.constructedCount=0 ∧ (combinationRecipe a).nodeCount=t.recipe.nodeCount
    | .mixed r p a => 0 < t.constructedCount ∧
        r.nodeCount+p.nodeCount+(combinationRecipe a).nodeCount+2+t.constructedCount ≤ t.recipe.nodeCount := by
  induction t with
  | constructed k r p =>
    have hk := k.nodeCount_pos
    simp only [group,constructedCount,recipe,Term.nodeCount]
    omega
  | honest i => exact ⟨rfl,rfl⟩
  | mul a b ia ib =>
    cases ha : a.group <;> cases hb : b.group <;>
      simp only [group,ha,hb,CiphertextGroup.merge,constructedCount,recipe,
        combinationRecipe,Combination.evaluate,Term.nodeCount] at ia ib ⊢ <;> omega

theorem mixed_constructedCount_pos (t : CiphertextAssembly n) {r p : Recipe 3}
    {a : Combination (HonestIndex n)} (hg : t.group = .mixed r p a) : 0 < t.constructedCount := by
  have h := t.group_occurrence_budget
  rw [hg] at h
  exact h.1

/-- Grouping a mixed assembly saves at least one node per public constructor
after the first. The honest combination uses its actual indexed recipe size. -/
theorem mixed_compression_cost (t : CiphertextAssembly n) {r p : Recipe 3}
    {a : Combination (HonestIndex n)} (hg : t.group = .mixed r p a) :
    (mixedCombinationRecipe r p a).nodeCount+t.constructedCount ≤ t.recipe.nodeCount+1 := by
  have h := t.group_occurrence_budget
  rw [hg] at h
  simp only [mixedCombinationRecipe,Term.nodeCount]
  omega

theorem mixed_compression_smaller (t : CiphertextAssembly n) {r p : Recipe 3}
    {a : Combination (HonestIndex n)} (hg : t.group = .mixed r p a)
    (hcount : 2 ≤ t.constructedCount) :
    (mixedCombinationRecipe r p a).nodeCount < t.recipe.nodeCount := by
  have h := t.mixed_compression_cost hg
  omega

theorem mixed_compression_public (t : CiphertextAssembly n) {restricted : Finset Nat}
    (hp : t.recipe.Public restricted) {r p : Recipe 3} {a : Combination (HonestIndex n)}
    (hg : t.group = .mixed r p a) : (mixedCombinationRecipe r p a).Public restricted := by
  have h := t.group_public hp
  rw [hg] at h
  exact mixedCombination_public r p h.1 h.2 a

end CiphertextAssembly
end ExplainableCrypto.Helios.Symbolic.Historical.General
