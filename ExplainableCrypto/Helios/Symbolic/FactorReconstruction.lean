import ExplainableCrypto.Helios.Symbolic.HomomorphicRootOverlap
import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

namespace BaseClass

/-- Multiplication in the existing E0 quotient; well-defined by congruence. -/
def mul (a b : BaseClass V) : BaseClass V :=
  Quotient.liftOn₂ a b (fun a b => (Term.binary .mul a b).baseClass)
    (fun _ _ _ _ ha hb => Quotient.sound (s := baseSetoid V) (.binary .mul ha hb))

instance : CommSemigroup (BaseClass V) where
  mul := mul
  mul_assoc a b c := Quotient.inductionOn₃ a b c fun a b c =>
    Quotient.sound (s := baseSetoid V) (.equation (.assoc .mul trivial a b c))
  mul_comm a b := Quotient.inductionOn₂ a b fun a b =>
    Quotient.sound (s := baseSetoid V) (.equation (.comm .mul trivial a b))

@[simp] theorem mk_mul (a b : Term V) :
    a.baseClass * b.baseClass = (Term.binary .mul a b).baseClass := rfl

end BaseClass

/-- The adjoined unit represents only an empty bookkeeping multiset. No term or
E0 equation is assigned to it. All actual terms fold to a non-unit value. -/
def factorProduct (s : Multiset (BaseClass V)) : WithOne (BaseClass V) :=
  (s.map fun x : BaseClass V => (x : WithOne (BaseClass V))).prod

theorem factorProduct_add (a b : Multiset (BaseClass V)) :
    factorProduct (a + b) = factorProduct a * factorProduct b := by
  simp [factorProduct, Multiset.prod_add]

/-- Reconstruct the exact E0 class from the outer factor multiset. -/
theorem Term.mulFactors_product (t : Term V) :
    factorProduct t.mulFactors = (t.baseClass : WithOne (BaseClass V)) := by
  induction t with
  | binary f a b ha hb =>
    cases f <;> first
      | exact (by rw [Term.mulFactors, factorProduct_add, ha, hb]; rfl)
      | simp [Term.mulFactors, factorProduct]
  | name => simp [Term.mulFactors, factorProduct]
  | var => simp [Term.mulFactors, factorProduct]
  | const => simp [Term.mulFactors, factorProduct]
  | unary => simp [Term.mulFactors, factorProduct]
  | ternary => simp [Term.mulFactors, factorProduct]
  | spk => simp [Term.mulFactors, factorProduct]

/-- Completeness is for exact E0 classes, not the executable factor-tag approximation. -/
theorem baseEq_iff_mulFactors (a b : Term V) : BaseEq a b ↔ a.mulFactors = b.mulFactors := by
  refine ⟨BaseEq.mul_factors, ?_⟩
  intro h
  have hp := congrArg factorProduct h
  rw [a.mulFactors_product, b.mulFactors_product] at hp
  exact (baseClass_eq_iff a b).mp (WithOne.coe_injective hp)

theorem Term.mulFactors_nonempty (t : Term V) : t.mulFactors ≠ 0 := by
  intro h
  have hp := congrArg factorProduct h
  rw [t.mulFactors_product] at hp
  simp [factorProduct] at hp

private theorem singleton_factor_representable (t : Term V)
    (ht : t.mulFactors = {t.baseClass}) {q : BaseClass V} (h : q ∈ t.mulFactors) :
    ∃ a : Term V, a.mulFactors = {q} := by
  rw [ht, Multiset.mem_singleton] at h
  exact ⟨t, h ▸ ht⟩

/-- Every individual outer factor has a representative that contributes exactly one factor. -/
theorem Term.factor_representable (t : Term V) {q : BaseClass V} (h : q ∈ t.mulFactors) :
    ∃ a : Term V, a.mulFactors = {q} := by
  induction t with
  | binary f a b ha hb =>
    by_cases hf : f = .mul
    · subst f
      rcases Multiset.mem_add.mp h with h | h
      · exact ha h
      · exact hb h
    · exact singleton_factor_representable (.binary f a b)
        (by cases f <;> simp_all [Term.mulFactors]) h
  | name n => exact singleton_factor_representable (.name n) rfl h
  | var v => exact singleton_factor_representable (.var v) rfl h
  | const c => exact singleton_factor_representable (.const c) rfl h
  | unary f a _ => exact singleton_factor_representable (.unary f a) rfl h
  | ternary f a b c _ _ _ => exact singleton_factor_representable (.ternary f a b c) rfl h
  | spk a b c d _ _ _ _ => exact singleton_factor_representable (.spk a b c d) rfl h

/-- Nonempty collections of representable individual factors can be multiplied.
The construction asserts existence, not a canonical order or executable quotient choice. -/
theorem factors_representable (s : Multiset (BaseClass V)) (hne : s ≠ 0)
    (hrep : ∀ q ∈ s, ∃ a : Term V, a.mulFactors = {q}) :
    ∃ a : Term V, a.mulFactors = s := by
  induction s using Multiset.induction_on with
  | empty => exact False.elim (hne rfl)
  | cons q s ih =>
    obtain ⟨a, ha⟩ := hrep q (by simp)
    by_cases hs : s = 0
    · subst s
      exact ⟨a, by simpa using ha⟩
    · obtain ⟨b, hb⟩ := ih hs (fun r hr => hrep r (by simp [hr]))
      refine ⟨.binary .mul a b, ?_⟩
      simp only [Term.mulFactors, ha, hb, Multiset.singleton_add]

theorem Term.subfactors_representable (t : Term V) (s : Multiset (BaseClass V))
    (hs : s ≤ t.mulFactors) (hne : s ≠ 0) : ∃ a : Term V, a.mulFactors = s :=
  factors_representable s hne (fun _ h => t.factor_representable (Multiset.mem_of_le hs h))

/-- Expose two ciphertexts anywhere among the outer factors, preserving a represented remainder. -/
theorem homomorphic_step_of_factors (t rest k r s m n : Term V)
    (h : t.mulFactors =
      {(.ternary .penc k r m : Term V).baseClass, (.ternary .penc k s n : Term V).baseClass} +
        rest.mulFactors) :
    ModuloStep t (.binary .mul (.ternary .penc k (.binary .compose r s) (.binary .add m n)) rest) := by
  have he : BaseEq t (.binary .mul (.binary .mul (.ternary .penc k r m) (.ternary .penc k s n)) rest) := by
    apply (baseEq_iff_mulFactors _ _).mpr
    simpa only [Term.mulFactors, Multiset.singleton_add, Multiset.insert_eq_cons] using h
  exact ((RootStep.homomorphic k r s m n).to_modulo.context (.binaryLeft .mul .hole rest)).pre_base he

/-- The empty remainder is handled without inventing an object-language identity. -/
theorem homomorphic_step_of_two_factors (t k r s m n : Term V)
    (h : t.mulFactors =
      {(.ternary .penc k r m : Term V).baseClass, (.ternary .penc k s n : Term V).baseClass}) :
    ModuloStep t (.ternary .penc k (.binary .compose r s) (.binary .add m n)) := by
  have he : BaseEq t (.binary .mul (.ternary .penc k r m) (.ternary .penc k s n)) := by
    apply (baseEq_iff_mulFactors _ _).mpr
    simpa only [Term.mulFactors, Multiset.singleton_add, Multiset.insert_eq_cons] using h
  exact (RootStep.homomorphic k r s m n).to_modulo.pre_base he

/-- Any selected ciphertext pair yields an actual step and exactly the residual factor bag.
The remainder may be empty. Its term representation is constructed, not assumed. -/
theorem homomorphic_selection_reachable (t k r s m n : Term V)
    (rest : Multiset (BaseClass V))
    (h : t.mulFactors =
      {(.ternary .penc k r m : Term V).baseClass, (.ternary .penc k s n : Term V).baseClass} + rest) :
    ∃ u, ModuloStep t u ∧ u.mulFactors =
      {(.ternary .penc k (.binary .compose r s) (.binary .add m n) : Term V).baseClass} + rest := by
  by_cases hr : rest = 0
  · subst rest
    refine ⟨.ternary .penc k (.binary .compose r s) (.binary .add m n), ?_, ?_⟩
    · exact homomorphic_step_of_two_factors t k r s m n (by simpa using h)
    · simp [Term.mulFactors]
  · have hsub : rest ≤ t.mulFactors := by rw [h]; exact Multiset.le_add_left _ _
    obtain ⟨tail, htail⟩ := t.subfactors_representable rest hsub hr
    refine ⟨.binary .mul (.ternary .penc k (.binary .compose r s) (.binary .add m n)) tail, ?_, ?_⟩
    · exact homomorphic_step_of_factors t tail k r s m n (by simpa only [htail] using h)
    · simp only [Term.mulFactors, htail]

namespace FactorReconstructionSPOT

/-- Zero is an ordinary factor, not the auxiliary fold identity. -/
theorem zero_not_multiplication_unit :
    ¬ BaseEq (Term.binary .mul (.name 0) (.const .zero) : Term Nat) (.name 0) := by
  intro h
  cases h.head_eq

/-- Equal factors still contribute twice to the multiset. -/
theorem repeated_factor_not_erased :
    (Term.binary .mul (.name 0) (.name 0) : Term Nat).mulFactors ≠
      (Term.name 0 : Term Nat).mulFactors := by
  intro h
  have hc := congrArg Multiset.card h
  simp [Term.mulFactors] at hc

abbrev first : Term Nat := .ternary .penc (.name 0) (.name 1) (.const .zero)
abbrev second : Term Nat := .ternary .penc (.name 0) (.name 2) (.const .one)
abbrev combined : Term Nat := .ternary .penc (.name 0)
  (.binary .compose (.name 1) (.name 2)) (.binary .add (.const .zero) (.const .one))

/-- E7 combines nonadjacent factors and retains the unrelated name. -/
theorem nonadjacent_ciphertexts_combine :
    ModuloStep (.binary .mul first (.binary .mul (.name 3) second))
      (.binary .mul combined (.name 3)) := by
  apply homomorphic_step_of_factors
  have he : BaseEq (.binary .mul first (.binary .mul (.name 3) second))
      (.binary .mul (.binary .mul first second) (.name 3)) :=
    (BaseEq.binary .mul (.refl _) (.equation (.comm .mul trivial _ _))).trans
      (BaseEq.equation (.assoc .mul trivial first second (.name 3))).symm
  simpa only [Term.mulFactors, Multiset.singleton_add, Multiset.insert_eq_cons] using he.mul_factors

/-- A two-factor product reduces to the ciphertext itself, without an added tail. -/
theorem two_ciphertexts_no_sentinel :
    ModuloStep (.binary .mul second first) combined := by
  apply homomorphic_step_of_two_factors
  simp [Term.mulFactors, Multiset.add_comm]

end FactorReconstructionSPOT
end ExplainableCrypto.Helios.Symbolic
