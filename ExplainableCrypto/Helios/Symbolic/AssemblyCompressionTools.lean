import ExplainableCrypto.Helios.Symbolic.AssemblyHandleTools

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.CiphertextAssembly
variable {n handles : Nat}

/-- Retained-handle assemblies inhabit the existing ciphertext syntax grammar. -/
theorem recipeWith_ciphertext_syntax (t : CiphertextAssembly n handles) (old : Fin 3 → Fin handles) :
    CiphertextRecipeSyntax (t.recipeWith old) := by
  induction t with
  | constructed k r p => exact .constructed k r p
  | honest i => exact .selected (old i.1.succ) (ProjectionChain.project _ i.2.val)
  | mul a b ia ib => exact .mul ia ib

/-- The selected key and grouped component bound fit the original assembly,
including all repeated keys and multiplication nodes. -/
theorem key_group_budgetWith (t : CiphertextAssembly n handles) (old : Fin 3 → Fin handles) :
    (t.keyRecipeWith old).nodeCount + t.group.budget ≤ (t.recipeWith old).nodeCount + 1 := by
  induction t with
  | constructed k r p => simp only [keyRecipeWith,group,CiphertextGroup.budget,recipeWith,Term.nodeCount]; omega
  | honest i =>
    have h := ((Term.var (old i.1.succ) : Recipe handles).drop i.2.val).nodeCount_pos
    simp only [keyRecipeWith,group,CiphertextGroup.budget,recipeWith,Term.project,Term.nodeCount]
    omega
  | mul a b ia _ =>
    have hb := b.group_budgetWith old
    have hm := CiphertextGroup.merge_budget a.group b.group
    simp only [keyRecipeWith,group,recipeWith,Term.nodeCount]
    omega

/-- A constructed-only multiplication saves at least one repeated key when
compressed. Both public component trees retain their full occurrence costs. -/
theorem constructed_mul_compression_smallerWith (a b : CiphertextAssembly n handles)
    (old : Fin 3 → Fin handles) {r p : Recipe handles} (hg : (a.mul b).group = .constructed r p) :
    (Term.ternary .penc ((a.mul b).keyRecipeWith old) r p).nodeCount < ((a.mul b).recipeWith old).nodeCount := by
  have ha := a.key_group_budgetWith old
  have hb := b.key_group_budgetWith old
  have hk := (b.keyRecipeWith old).nodeCount_pos
  cases hga : a.group <;> cases hgb : b.group <;>
    simp only [group,hga,hgb,CiphertextGroup.merge] at hg <;> cases hg
  rw [hga] at ha
  rw [hgb] at hb
  simp only [CiphertextGroup.budget,keyRecipeWith,recipeWith,Term.nodeCount] at ha hb ⊢
  omega

theorem constructed_compression_publicWith (t : CiphertextAssembly n handles) (old : Fin 3 → Fin handles)
    {restricted : Finset Nat} (hp : (t.recipeWith old).Public restricted) {r p : Recipe handles}
    (hg : t.group = .constructed r p) : (Term.ternary .penc (t.keyRecipeWith old) r p).Public restricted := by
  have hgp := t.group_publicWith old hp
  rw [hg] at hgp
  exact ⟨t.keyRecipeWith_public old hp,hgp⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.CiphertextAssembly
