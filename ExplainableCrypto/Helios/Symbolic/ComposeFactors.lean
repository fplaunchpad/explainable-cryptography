import ExplainableCrypto.Helios.Symbolic.FactorReconstruction

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Flatten only outer nonce composition, retaining exact E0 classes and multiplicity. -/
def Term.composeFactors : Term V → Multiset (BaseClass V)
  | .binary .compose a b => a.composeFactors + b.composeFactors
  | t => {t.baseClass}

theorem BaseEquation.compose_factors {a b : Term V} (h : BaseEquation a b) :
    a.composeFactors = b.composeFactors := by
  cases h with
  | zero_one => exact congrArg (fun x => ({x} : Multiset (BaseClass V))) (Quotient.sound (.equation .zero_one))
  | zero_zero => exact congrArg (fun x => ({x} : Multiset (BaseClass V))) (Quotient.sound (.equation .zero_zero))
  | comm f hf a b =>
    cases f <;> try exact congrArg (fun x => ({x} : Multiset (BaseClass V))) (Quotient.sound (.equation (.comm _ hf a b)))
    simpa only [Term.composeFactors] using Multiset.add_comm a.composeFactors b.composeFactors
  | assoc f hf a b c =>
    cases f <;> try exact congrArg (fun x => ({x} : Multiset (BaseClass V))) (Quotient.sound (.equation (.assoc _ hf a b c)))
    simpa only [Term.composeFactors] using Multiset.add_assoc a.composeFactors b.composeFactors c.composeFactors

theorem BaseEq.compose_factors {a b : Term V} (h : BaseEq a b) : a.composeFactors = b.composeFactors := by
  induction h with
  | equation h => exact h.compose_factors
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | unary f h => exact congrArg (fun x => ({x} : Multiset (BaseClass V))) (Quotient.sound (.unary f h))
  | binary f ha hb ih₁ ih₂ =>
    cases f <;> first
      | exact congrArg₂ (· + ·) ih₁ ih₂
      | exact congrArg (fun x => ({x} : Multiset (BaseClass V))) (Quotient.sound (.binary _ ha hb))
  | ternary f ha hb hc => exact congrArg (fun x => ({x} : Multiset (BaseClass V))) (Quotient.sound (.ternary f ha hb hc))
  | spk ha hb hc hd => exact congrArg (fun x => ({x} : Multiset (BaseClass V))) (Quotient.sound (.spk ha hb hc hd))

section CompositionFold

/-- This instance is local to reconstruction. Exported quotient multiplication
continues to mean the term's multiplication constructor. -/
local instance composeSemigroup : CommSemigroup (BaseClass V) where
  mul a b := Quotient.liftOn₂ a b (fun a b => (Term.binary .compose a b).baseClass)
    (fun _ _ _ _ ha hb => Quotient.sound (s := baseSetoid V) (.binary .compose ha hb))
  mul_assoc a b c := Quotient.inductionOn₃ a b c fun a b c =>
    Quotient.sound (s := baseSetoid V) (.equation (.assoc .compose trivial a b c))
  mul_comm a b := Quotient.inductionOn₂ a b fun a b =>
    Quotient.sound (s := baseSetoid V) (.equation (.comm .compose trivial a b))

private def composeProduct (s : Multiset (BaseClass V)) : WithOne (BaseClass V) :=
  (s.map fun x : BaseClass V => (x : WithOne (BaseClass V))).prod

private theorem composeProduct_add (a b : Multiset (BaseClass V)) :
    composeProduct (a + b) = composeProduct a * composeProduct b := by
  simp [composeProduct, Multiset.prod_add]

private theorem composeFactors_reconstruct (t : Term V) :
    composeProduct t.composeFactors = (t.baseClass : WithOne (BaseClass V)) := by
  induction t with
  | binary f a b ha hb =>
    cases f <;> first
      | exact (by rw [Term.composeFactors, composeProduct_add, ha, hb]; rfl)
      | simp [Term.composeFactors, composeProduct]
  | name => simp [Term.composeFactors, composeProduct]
  | var => simp [Term.composeFactors, composeProduct]
  | const => simp [Term.composeFactors, composeProduct]
  | unary => simp [Term.composeFactors, composeProduct]
  | ternary => simp [Term.composeFactors, composeProduct]
  | spk => simp [Term.composeFactors, composeProduct]

/-- Reconstruction is for exact E0 classes, not an executable quotient comparison. -/
theorem baseEq_iff_composeFactors (a b : Term V) : BaseEq a b ↔ a.composeFactors = b.composeFactors := by
  refine ⟨BaseEq.compose_factors, ?_⟩
  intro h
  have hp := congrArg composeProduct h
  rw [composeFactors_reconstruct a, composeFactors_reconstruct b] at hp
  exact (baseClass_eq_iff a b).mp (WithOne.coe_injective hp)

/-- No actual term denotes the fold's auxiliary identity. -/
theorem Term.composeFactors_nonempty (t : Term V) : t.composeFactors ≠ 0 := by
  intro h
  have hp := congrArg composeProduct h
  rw [composeFactors_reconstruct t] at hp
  simp [composeProduct] at hp

end CompositionFold

private theorem compose_singleton_representable (t : Term V)
    (ht : t.composeFactors = {t.baseClass}) {q : BaseClass V} (h : q ∈ t.composeFactors) :
    ∃ a : Term V, a.composeFactors = {q} := by
  rw [ht, Multiset.mem_singleton] at h
  exact ⟨t, h ▸ ht⟩

theorem Term.compose_factor_representable (t : Term V) {q : BaseClass V} (h : q ∈ t.composeFactors) :
    ∃ a : Term V, a.composeFactors = {q} := by
  induction t with
  | binary f a b ha hb =>
    by_cases hf : f = .compose
    · subst f
      rcases Multiset.mem_add.mp h with h | h
      · exact ha h
      · exact hb h
    · exact compose_singleton_representable (.binary f a b)
        (by cases f <;> simp_all [Term.composeFactors]) h
  | name n => exact compose_singleton_representable (.name n) rfl h
  | var v => exact compose_singleton_representable (.var v) rfl h
  | const c => exact compose_singleton_representable (.const c) rfl h
  | unary f a _ => exact compose_singleton_representable (.unary f a) rfl h
  | ternary f a b c _ _ _ => exact compose_singleton_representable (.ternary f a b c) rfl h
  | spk a b c d _ _ _ _ => exact compose_singleton_representable (.spk a b c d) rfl h

theorem compose_factors_representable (s : Multiset (BaseClass V)) (hne : s ≠ 0)
    (hrep : ∀ q ∈ s, ∃ a : Term V, a.composeFactors = {q}) :
    ∃ a : Term V, a.composeFactors = s := by
  induction s using Multiset.induction_on with
  | empty => exact False.elim (hne rfl)
  | cons q s ih =>
    obtain ⟨a, ha⟩ := hrep q (by simp)
    by_cases hs : s = 0
    · subst s
      exact ⟨a, by simpa using ha⟩
    · obtain ⟨b, hb⟩ := ih hs (fun r hr => hrep r (by simp [hr]))
      refine ⟨.binary .compose a b, ?_⟩
      simp only [Term.composeFactors, ha, hb, Multiset.singleton_add]

theorem Term.compose_subfactors_representable (t : Term V) (s : Multiset (BaseClass V))
    (hs : s ≤ t.composeFactors) (hne : s ≠ 0) : ∃ a : Term V, a.composeFactors = s :=
  compose_factors_representable s hne (fun _ h => t.compose_factor_representable (Multiset.mem_of_le hs h))

end ExplainableCrypto.Helios.Symbolic
