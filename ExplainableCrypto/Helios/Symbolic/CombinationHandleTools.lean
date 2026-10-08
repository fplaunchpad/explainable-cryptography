import ExplainableCrypto.Helios.Symbolic.AssemblyHandleTools
import ExplainableCrypto.Helios.Symbolic.HonestProductMinima

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n handles : Nat}

/-- Reuse the initial honest combination through an explicit old-handle map. -/
def combinationRecipeWith (old : Fin 3 → Fin handles) (a : Combination (HonestIndex n)) : Recipe handles :=
  (combinationRecipe a).subst (fun i => .var (old i))

/-- Honest selectors mention no literal names under any handle map. -/
theorem combinationRecipeWith_public (old : Fin 3 → Fin handles) (restricted : Finset Nat)
    (a : Combination (HonestIndex n)) : (combinationRecipeWith old a).Public restricted := by
  induction a with
  | leaf i =>
    simpa only [combinationRecipeWith,combinationRecipe,Combination.evaluate,Term.subst_project,Term.subst] using
      (show (Term.var (old i.1.succ) : Recipe handles).Public restricted from trivial).project i.2.val
  | mul a b ia ib => exact ⟨ia,ib⟩

/-- Renaming old handles preserves exact honest selector costs. -/
theorem combinationRecipeWith_nodeCount (old : Fin 3 → Fin handles) (a : Combination (HonestIndex n)) :
    (combinationRecipeWith old a).nodeCount = (combinationRecipe a).nodeCount := by
  induction a with
  | leaf i => simp [combinationRecipeWith,combinationRecipe,Combination.evaluate,Term.subst_project,Term.subst,Term.project_nodeCount,Term.nodeCount]
  | mul a b ia ib =>
    simp only [combinationRecipeWith,combinationRecipe,Combination.evaluate,Term.subst,Term.nodeCount] at *
    omega

/-- An honest group records the exact original selector tree, for every
handle map. Grouping cannot erase a constructed contribution. -/
theorem CiphertextAssembly.recipeWith_of_honest_group (t : CiphertextAssembly n handles)
    (old : Fin 3 → Fin handles) {a : Combination (HonestIndex n)} (hg : t.group = .honest a) :
    t.recipeWith old = combinationRecipeWith old a := by
  induction t generalizing a with
  | constructed k r p => cases hg
  | honest i =>
    cases hg
    simp only [CiphertextAssembly.recipeWith,combinationRecipeWith,combinationRecipe,Combination.evaluate,Term.subst_project,Term.subst]
  | mul t u it iu =>
    cases ht : t.group <;> cases hu : u.group <;>
      simp only [CiphertextAssembly.group,ht,hu,CiphertextGroup.merge] at hg <;> cases hg
    exact congrArg₂ (Term.binary .mul) (it ht) (iu hu)

end ExplainableCrypto.Helios.Symbolic.Historical.General
