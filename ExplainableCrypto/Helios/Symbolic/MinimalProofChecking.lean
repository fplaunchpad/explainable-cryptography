import ExplainableCrypto.Helios.Symbolic.ProofCheckPaths
import ExplainableCrypto.Helios.Symbolic.MinimalRecipes

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type} {restricted : Finset Nat} {σ : V → Term W}

/-- The public constant ok is strictly smaller than any checking recipe. -/
theorem MinimalRecipe.check_not_ok (a b c : Term V)
    (h : MinimalRecipe restricted σ (.ternary .checkspk a b c)) :
    ¬ EqE ((.ternary .checkspk a b c : Term V).subst σ) (.const .ok) := by
  intro he
  apply h.no_smaller (s := .const .ok) trivial he
  have := a.nodeCount_pos
  simp only [Term.nodeCount]
  omega

theorem MinimalRecipe.no_proof_check_match (a b c : Term V)
    (h : MinimalRecipe restricted σ (.ternary .checkspk a b c)) :
    ¬ ProofCheckMatch (a.subst σ) (b.subst σ) (c.subst σ) :=
  fun hm => h.check_not_ok a b c hm.reduces.sound

/-- All minimum checking paths retain their constructor and component paths. -/
theorem MinimalRecipe.proof_check_path (a b c : Term V)
    (h : MinimalRecipe restricted σ (.ternary .checkspk a b c))
    {t : Term W} (ht : ReducesModulo ((.ternary .checkspk a b c : Term V).subst σ) t) :
    ∃ a' b' c', ReducesModulo (a.subst σ) a' ∧ ReducesModulo (b.subst σ) b' ∧
      ReducesModulo (c.subst σ) c' ∧ BaseEq t (.ternary .checkspk a' b' c') := by
  rcases ht.proof_check_cases with hs | ⟨hm, _⟩
  · exact hs
  · exact False.elim (h.no_proof_check_match a b c hm)

theorem MinimalRecipe.proof_check_normal_shape (a b c : Term V)
    (h : MinimalRecipe restricted σ (.ternary .checkspk a b c))
    {t : Term W} (ht : Irreducible t)
    (he : EqE ((.ternary .checkspk a b c : Term V).subst σ) t) :
    ∃ a' b' c', t = .ternary .checkspk a' b' c' ∧
      EqE (a.subst σ) a' ∧ EqE (b.subst σ) b' ∧ EqE (c.subst σ) c' :=
  proof_check_normal_shape_of_no_match _ _ _ (h.no_proof_check_match a b c) ht he

/-- Normal-form composition for the complete checking recipe case: the frame,
substitution and public-name policy are arbitrary. Normal values remain explicit. -/
theorem MinimalRecipe.proof_check_normal_form (a b c : Term V)
    (h : MinimalRecipe restricted σ (.ternary .checkspk a b c))
    {a' b' c' t : Term W} (ha : Irreducible a') (hb : Irreducible b') (hc : Irreducible c')
    (ht : Irreducible t) (hea : EqE (a.subst σ) a') (heb : EqE (b.subst σ) b')
    (hec : EqE (c.subst σ) c')
    (he : EqE ((.ternary .checkspk a b c : Term V).subst σ) t) :
    BaseEq t (.ternary .checkspk a' b' c') :=
  proof_check_normal_form_of_no_match _ _ _ (h.no_proof_check_match a b c)
    ha hb hc ht hea heb hec he

end ExplainableCrypto.Helios.Symbolic
