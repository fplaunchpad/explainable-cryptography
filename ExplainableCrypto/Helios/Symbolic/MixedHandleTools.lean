import ExplainableCrypto.Helios.Symbolic.CombinationHandleTools
import ExplainableCrypto.Helios.Symbolic.MixedCompression

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n handles : Nat}

/-- One public-key constructor multiplied by the retained honest combination. -/
def mixedCombinationRecipeWith (old : Fin 3 → Fin handles) (r p : Recipe handles)
    (a : Combination (HonestIndex n)) : Recipe handles :=
  .binary .mul (.ternary .penc (.var (old 0)) r p) (combinationRecipeWith old a)

theorem mixedCombinationRecipeWith_public (old : Fin 3 → Fin handles) {restricted : Finset Nat}
    (r p : Recipe handles) (hr : r.Public restricted) (hp : p.Public restricted)
    (a : Combination (HonestIndex n)) : (mixedCombinationRecipeWith old r p a).Public restricted :=
  ⟨⟨trivial,hr,hp⟩,combinationRecipeWith_public old restricted a⟩

namespace CiphertextAssembly

/-- All public component occurrences and exact honest selector costs fit in
the source syntax. Each extra constructor pays for a fusion saving. -/
theorem group_occurrence_budgetWith (t : CiphertextAssembly n handles) (old : Fin 3 → Fin handles) :
    match t.group with
    | .constructed r p => 0 < t.constructedCount ∧
        r.nodeCount+p.nodeCount+1+t.constructedCount ≤ (t.recipeWith old).nodeCount
    | .honest a => t.constructedCount=0 ∧ (combinationRecipe a).nodeCount=(t.recipeWith old).nodeCount
    | .mixed r p a => 0 < t.constructedCount ∧
        r.nodeCount+p.nodeCount+(combinationRecipe a).nodeCount+2+t.constructedCount ≤ (t.recipeWith old).nodeCount := by
  induction t with
  | constructed k r p =>
    have hk := k.nodeCount_pos
    simp only [group,constructedCount,recipeWith,Term.nodeCount]
    omega
  | honest i =>
    refine ⟨rfl,?_⟩
    simp only [combinationRecipe,Combination.evaluate,recipeWith,Term.project_nodeCount,Term.nodeCount]
  | mul a b ia ib =>
    cases ha : a.group <;> cases hb : b.group <;>
      simp only [group,ha,hb,CiphertextGroup.merge,constructedCount,recipeWith,
        combinationRecipe,Combination.evaluate,Term.nodeCount] at ia ib ⊢ <;> omega

theorem mixed_constructedCount_posWith (t : CiphertextAssembly n handles) (old : Fin 3 → Fin handles)
    {r p : Recipe handles} {a : Combination (HonestIndex n)} (hg : t.group = .mixed r p a) :
    0 < t.constructedCount := by
  have h := t.group_occurrence_budgetWith old
  rw [hg] at h
  exact h.1

/-- Mixed grouping saves at least one node per constructor after the first. -/
theorem mixed_compression_costWith (t : CiphertextAssembly n handles) (old : Fin 3 → Fin handles)
    {r p : Recipe handles} {a : Combination (HonestIndex n)} (hg : t.group = .mixed r p a) :
    (mixedCombinationRecipeWith old r p a).nodeCount+t.constructedCount ≤ (t.recipeWith old).nodeCount+1 := by
  have h := t.group_occurrence_budgetWith old
  rw [hg] at h
  simp only [mixedCombinationRecipeWith,Term.nodeCount,combinationRecipeWith_nodeCount]
  omega

theorem mixed_compression_smallerWith (t : CiphertextAssembly n handles) (old : Fin 3 → Fin handles)
    {r p : Recipe handles} {a : Combination (HonestIndex n)} (hg : t.group = .mixed r p a)
    (hcount : 2 ≤ t.constructedCount) :
    (mixedCombinationRecipeWith old r p a).nodeCount < (t.recipeWith old).nodeCount := by
  have h := t.mixed_compression_costWith old hg
  omega

theorem mixed_compression_publicWith (t : CiphertextAssembly n handles) (old : Fin 3 → Fin handles)
    {restricted : Finset Nat} (hp : (t.recipeWith old).Public restricted)
    {r p : Recipe handles} {a : Combination (HonestIndex n)} (hg : t.group = .mixed r p a) :
    (mixedCombinationRecipeWith old r p a).Public restricted := by
  have h := t.group_publicWith old hp
  rw [hg] at h
  exact mixedCombinationRecipeWith_public old r p h.1 h.2 a

end CiphertextAssembly
end ExplainableCrypto.Helios.Symbolic.Historical.General
