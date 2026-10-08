import ExplainableCrypto.Helios.Symbolic.MinimalRecipes
import ExplainableCrypto.Helios.Symbolic.ProjectionPaths

namespace ExplainableCrypto.Helios.Symbolic.MinimalRecipeSPOT

/-- This non-atomic minimum cannot be replaced by any size-one recipe. -/
theorem public_key_minimal :
    MinimalRecipe {10} (Term.var : Nat → Term Nat) (.unary .pk (.const .zero)) := by
  refine ⟨trivial, ?_⟩
  intro s _ he
  simp only [Term.subst_var] at he
  change 2 ≤ s.nodeCount
  cases s with
  | name n =>
    obtain ⟨_, hh, _⟩ := he.pk_irreducible_shape (name_irreducible n)
    cases hh
  | var n =>
    obtain ⟨_, hh, _⟩ := he.pk_irreducible_shape (var_irreducible n)
    cases hh
  | const c =>
    obtain ⟨_, hh, _⟩ := he.pk_irreducible_shape (constant_irreducible c)
    cases hh
  | unary f a => have := a.nodeCount_pos; simp only [Term.nodeCount]; omega
  | binary f a b => have := a.nodeCount_pos; simp only [Term.nodeCount]; omega
  | ternary f a b c => have := a.nodeCount_pos; simp only [Term.nodeCount]; omega
  | spk a b c d => have := a.nodeCount_pos; simp only [Term.nodeCount]; omega

theorem public_key_subterm_minimal :
    MinimalRecipe {10} (Term.var : Nat → Term Nat) (.const .zero) :=
  public_key_minimal.subterm (.unary .pk .hole)

/-- The minimized PBT failure: a smallest recipe can conceal a raw redex in its handle. -/
theorem minimum_can_evaluate_to_redex :
    let σ : Nat → Term Nat := fun _ => .unary .fst (.binary .pair (.name 0) (.const .zero))
    MinimalRecipe {10} σ (.var 0) ∧
      RewriteStep ((Term.var 0).subst σ) (.name 0) ∧
      ¬ RawIrreducible ((Term.var 0).subst σ) := by
  dsimp
  have hs := (RootStep.fst (.name (V := Nat) 0) (.const .zero)).to_rewrite
  exact ⟨MinimalRecipe.of_nodeCount_one trivial rfl, hs, fun h => h _ hs⟩

/-- Literal restricted names are excluded even at the absolute lower size bound. -/
theorem forbidden_atom_not_minimal :
    ¬ MinimalRecipe {10} (Term.var : Nat → Term Nat) (.name 10) := by
  intro h
  have hp := h.isPublic
  simp [Term.Public] at hp

abbrev keys : Nat → Term Nat := fun _ => .unary .pk (.name 0)
abbrev semanticDecrypt : Term Nat :=
  .binary .dec (.name 0) (.ternary .penc (.var 0) (.name 1) (.const .one))

/-- Raw irreducibility alone does not establish minimality under a substitution. -/
theorem semantic_match_refutes_minimum :
    RawIrreducible semanticDecrypt ∧ ¬ MinimalRecipe {10} keys semanticDecrypt := by
  refine ⟨?_, MinimalRecipe.not_decrypt_ciphertext _ _ _ _ (.refl _)⟩
  have he : normalizeRaw semanticDecrypt = semanticDecrypt := by decide
  simpa only [he] using normalizeRaw_irreducible semanticDecrypt

/-- Distinct key handles with the same value still permit E7 to shorten a product. -/
theorem duplicate_semantic_keys_not_minimal :
    ¬ MinimalRecipe {10} keys
      (.binary .mul (.ternary .penc (.var 0) (.name 1) (.const .zero))
        (.ternary .penc (.var 1) (.name 2) (.const .one))) :=
  MinimalRecipe.not_ciphertext_product _ _ _ _ _ _ (.refl _)

/-- E6 needs agreement of its ciphertext copies, including after handle expansion. -/
theorem semantic_partial_decryption_not_minimal :
    let σ : Nat → Term Nat := fun _ => .ternary .penc (.unary .pk (.name 0)) (.name 1) (.const .one)
    ¬ MinimalRecipe {10} σ
      (.binary .dec (.binary .partialDecrypt (.name 0)
        (.ternary .penc (.unary .pk (.name 0)) (.name 1) (.const .one))) (.var 0)) :=
  MinimalRecipe.not_partial_decryption _ _ _ _ _ (.refl _) (.refl _)

/-- The existential result covers an actual reducible public recipe and preserves its value. -/
theorem projection_has_minimum :
    ∃ s : Term Nat, MinimalRecipe {10} Term.var s ∧
      EqE (.unary .fst (.binary .pair (.const .one) (.const .zero))) s := by
  simpa only [Term.subst_var] using
    (exists_minimal_recipe (σ := (Term.var : Nat → Term Nat))
      (.unary .fst (.binary .pair (.const .one) (.const .zero))) (by trivial :
        (.unary .fst (.binary .pair (.const .one) (.const .zero)) : Term Nat).Public {10}))

/-- E0-equivalent representatives can have different sizes; raw normality is insufficient. -/
theorem zero_expansion_not_minimal :
    BaseEq (Term.binary (V := Nat) .add (.const .zero) (.const .zero)) (.const .zero) ∧
      ¬ MinimalRecipe {10} (Term.var : Nat → Term Nat)
        (.binary .add (.const .zero) (.const .zero)) := by
  refine ⟨.equation .zero_zero, ?_⟩
  intro h
  exact h.no_smaller (s := .const .zero) trivial (EqE.equation .zero_zero) (by decide)

end ExplainableCrypto.Helios.Symbolic.MinimalRecipeSPOT
