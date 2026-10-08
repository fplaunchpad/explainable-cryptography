import ExplainableCrypto.Helios.Symbolic.FactorReconstruction
import ExplainableCrypto.Helios.Symbolic.RootReduction
import ExplainableCrypto.Helios.Symbolic.HomomorphicOverlap

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

abbrev ciphertextPairFactors (k r s m n : Term V) : Multiset (BaseClass V) :=
  {(.ternary .penc k r m : Term V).baseClass, (.ternary .penc k s n : Term V).baseClass}

abbrev combinedCiphertext (k r s m n : Term V) : Term V :=
  .ternary .penc k (.binary .compose r s) (.binary .add m n)

private theorem factor_shuffle (a b c : Multiset (BaseClass V)) : a + (b + c) = b + (a + c) := by
  rw [← Multiset.add_assoc, Multiset.add_comm a b, Multiset.add_assoc]

/-- Disjoint occurrence selections in any E0 representative. Branch factor bags
identify which pair was reduced and retain the entire remainder. Keys may differ. -/
theorem disjoint_homomorphic_selections_joined
    (t k₁ r₁ s₁ m₁ n₁ k₂ r₂ s₂ m₂ n₂ : Term V) (rest : Multiset (BaseClass V))
    (h : t.mulFactors = ciphertextPairFactors k₁ r₁ s₁ m₁ n₁ +
      (ciphertextPairFactors k₂ r₂ s₂ m₂ n₂ + rest)) :
    ∃ u v,
      ModuloStep t u ∧ u.mulFactors = {(combinedCiphertext k₁ r₁ s₁ m₁ n₁).baseClass} +
        (ciphertextPairFactors k₂ r₂ s₂ m₂ n₂ + rest) ∧
      ModuloStep t v ∧ v.mulFactors = {(combinedCiphertext k₂ r₂ s₂ m₂ n₂).baseClass} +
        (ciphertextPairFactors k₁ r₁ s₁ m₁ n₁ + rest) ∧ JoinModulo u v := by
  obtain ⟨u, htu, hu⟩ := homomorphic_selection_reachable t k₁ r₁ s₁ m₁ n₁ _ h
  have h' : t.mulFactors = ciphertextPairFactors k₂ r₂ s₂ m₂ n₂ +
      (ciphertextPairFactors k₁ r₁ s₁ m₁ n₁ + rest) := h.trans (factor_shuffle _ _ _)
  obtain ⟨v, htv, hv⟩ := homomorphic_selection_reachable t k₂ r₂ s₂ m₂ n₂ _ h'
  have hu' := hu.trans (factor_shuffle _ _ _)
  have hv' := hv.trans (factor_shuffle _ _ _)
  obtain ⟨u', huu', hu'fac⟩ := homomorphic_selection_reachable u k₂ r₂ s₂ m₂ n₂ _ hu'
  obtain ⟨v', hvv', hv'fac⟩ := homomorphic_selection_reachable v k₁ r₁ s₁ m₁ n₁ _ hv'
  have he : BaseEq u' v' := (baseEq_iff_mulFactors _ _).mpr
    (hu'fac.trans ((factor_shuffle _ _ _).trans hv'fac.symm))
  exact ⟨u, v, htu, hu, htv, hv, ⟨v', .single (huu'.post_base he), .single hvv'⟩⟩

private theorem factor_pair_rotate (a b c : BaseClass V) (rest : Multiset (BaseClass V)) :
    {a, b} + ({c} + rest) = {b, c} + ({a} + rest) := by
  simp only [Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add]
  rw [Multiset.cons_swap a b, Multiset.cons_swap a c]

/-- Shared-factor selections in an arbitrary E0 representative and arbitrary remainder.
The two branch bags distinguish first-two and last-two fusion. -/
theorem shared_homomorphic_selections_joined (a k r s t m n p : Term V)
    (rest : Multiset (BaseClass V))
    (h : a.mulFactors = ciphertextPairFactors k r s m n +
      ({(Term.ternary .penc k t p).baseClass} + rest)) :
    ∃ u v,
      ModuloStep a u ∧ u.mulFactors = {(combinedCiphertext k r s m n).baseClass} +
        ({(Term.ternary .penc k t p).baseClass} + rest) ∧
      ModuloStep a v ∧ v.mulFactors = {(combinedCiphertext k s t n p).baseClass} +
        ({(Term.ternary .penc k r m).baseClass} + rest) ∧ JoinModulo u v := by
  obtain ⟨u, hau, hu⟩ := homomorphic_selection_reachable a k r s m n _ h
  have h' := h.trans (factor_pair_rotate _ _ _ rest)
  obtain ⟨v, hav, hv⟩ := homomorphic_selection_reachable a k s t n p _ h'
  have hu' : u.mulFactors = ciphertextPairFactors k (.binary .compose r s) t (.binary .add m n) p + rest := by
    simpa only [ciphertextPairFactors, Multiset.insert_eq_cons, Multiset.cons_add,
      Multiset.singleton_add] using hu
  have hv' : v.mulFactors = ciphertextPairFactors k r (.binary .compose s t) m (.binary .add n p) + rest := by
    simpa only [ciphertextPairFactors, Multiset.insert_eq_cons, Multiset.cons_add,
      Multiset.singleton_add] using hv.trans (factor_shuffle _ _ _)
  obtain ⟨u', huu', hu'fac⟩ := homomorphic_selection_reachable u k (.binary .compose r s) t (.binary .add m n) p rest hu'
  obtain ⟨v', hvv', hv'fac⟩ := homomorphic_selection_reachable v k r (.binary .compose s t) m (.binary .add n p) rest hv'
  have he := (baseClass_eq_iff (tripleFinalLeft k r s t m n p) (tripleFinal k r s t m n p)).mpr
    (triple_endpoints_base k r s t m n p)
  have hbase : BaseEq u' v' := (baseEq_iff_mulFactors _ _).mpr
    (hu'fac.trans ((congrArg (fun q => ({q} : Multiset (BaseClass V)) + rest) he).trans hv'fac.symm))
  exact ⟨u, v, hau, hu, hav, hv, ⟨v', .single (huu'.post_base hbase), .single hvv'⟩⟩

namespace FactorSelectionSPOT

abbrev a : Term Nat := .ternary .penc (.name 0) (.name 2) (.const .zero)
abbrev b : Term Nat := .ternary .penc (.name 0) (.name 3) (.const .one)
abbrev c : Term Nat := .ternary .penc (.name 1) (.name 2) (.const .one)
abbrev d : Term Nat := .ternary .penc (.name 1) (.name 3) (.const .zero)
abbrev ab : Term Nat := combinedCiphertext (.name 0) (.name 2) (.name 3) (.const .zero) (.const .one)
abbrev cd : Term Nat := combinedCiphertext (.name 1) (.name 2) (.name 3) (.const .one) (.const .zero)

/-- Literal distinct-key control: each branch retains the other key group's pair. -/
theorem different_key_groups_join :
    ∃ u v, ModuloStep (.binary .mul (.binary .mul a b) (.binary .mul c d)) u ∧
      u.mulFactors = {ab.baseClass} + {c.baseClass, d.baseClass} ∧
      ModuloStep (.binary .mul (.binary .mul a b) (.binary .mul c d)) v ∧
      v.mulFactors = {cd.baseClass} + {a.baseClass, b.baseClass} ∧ JoinModulo u v := by
  have h := disjoint_homomorphic_selections_joined
    (.binary .mul (.binary .mul a b) (.binary .mul c d))
    (.name 0) (.name 2) (.name 3) (.const .zero) (.const .one)
    (.name 1) (.name 2) (.name 3) (.const .one) (.const .zero) 0
    (by simp [Term.mulFactors, ciphertextPairFactors, a, b, c, d])
  simpa using h

abbrev e : Term Nat := .ternary .penc (.name 0) (.name 4) (.const .zero)
abbrev be : Term Nat := combinedCiphertext (.name 0) (.name 3) (.name 4) (.const .one) (.const .zero)

/-- The shared-factor peak retains an unrelated name on both branches. -/
theorem shared_pair_retains_remainder :
    ∃ u v, ModuloStep (.binary .mul (.binary .mul a b) (.binary .mul e (.name 9))) u ∧
      u.mulFactors = {ab.baseClass} + ({e.baseClass} + {(Term.name 9 : Term Nat).baseClass}) ∧
      ModuloStep (.binary .mul (.binary .mul a b) (.binary .mul e (.name 9))) v ∧
      v.mulFactors = {be.baseClass} + ({a.baseClass} + {(Term.name 9 : Term Nat).baseClass}) ∧
      JoinModulo u v := by
  exact shared_homomorphic_selections_joined
    (.binary .mul (.binary .mul a b) (.binary .mul e (.name 9)))
    (.name 0) (.name 2) (.name 3) (.name 4) (.const .zero) (.const .one) (.const .zero)
    {(Term.name 9 : Term Nat).baseClass}
    (by simp [Term.mulFactors, ciphertextPairFactors, a, b, e])

/-- The two groups cannot instead be combined by a wrong-key root matcher. -/
theorem cross_key_pair_no_match : (rootReduce (.binary .mul a c)).map Subtype.val = none := by
  decide

end FactorSelectionSPOT
end ExplainableCrypto.Helios.Symbolic
