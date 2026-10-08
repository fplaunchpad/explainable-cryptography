import ExplainableCrypto.Helios.Symbolic.RigidRootOverlap
import Mathlib.Data.Multiset.ZeroCons

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- A quotient used for metatheory factor accounting, not an executable normaliser. -/
def baseSetoid (V : Type) : Setoid (Term V) where
  r := BaseEq
  iseqv := ⟨BaseEq.refl, BaseEq.symm, BaseEq.trans⟩

abbrev BaseClass (V : Type) := Quotient (baseSetoid V)

def Term.baseClass (t : Term V) : BaseClass V := Quotient.mk (baseSetoid V) t

theorem baseClass_eq_iff (a b : Term V) : a.baseClass = b.baseClass ↔ BaseEq a b :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound (s := baseSetoid V) h⟩

/-- Flatten only the outer multiplication; every other term remains one E0 class. -/
def Term.mulFactors : Term V → Multiset (BaseClass V)
  | .binary .mul a b => a.mulFactors + b.mulFactors
  | t => {t.baseClass}

theorem BaseEquation.mul_factors {a b : Term V} (h : BaseEquation a b) :
    a.mulFactors = b.mulFactors := by
  cases h with
  | zero_one => exact congrArg (fun x => ({x} : Multiset (BaseClass V))) (Quotient.sound (.equation .zero_one))
  | zero_zero => exact congrArg (fun x => ({x} : Multiset (BaseClass V))) (Quotient.sound (.equation .zero_zero))
  | comm f hf a b =>
    cases f <;> try exact congrArg (fun x => ({x} : Multiset (BaseClass V))) (Quotient.sound (.equation (.comm _ hf a b)))
    simpa only [Term.mulFactors] using Multiset.add_comm a.mulFactors b.mulFactors
  | assoc f hf a b c =>
    cases f <;> try exact congrArg (fun x => ({x} : Multiset (BaseClass V))) (Quotient.sound (.equation (.assoc _ hf a b c)))
    simpa only [Term.mulFactors] using Multiset.add_assoc a.mulFactors b.mulFactors c.mulFactors

/-- Arbitrary E0 congruence, including equations inside any factor, preserves the bag. -/
theorem BaseEq.mul_factors {a b : Term V} (h : BaseEq a b) : a.mulFactors = b.mulFactors := by
  induction h with
  | equation h => exact h.mul_factors
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

private theorem pair_matching {α : Type} {a b c d : α}
    (h : ({a, b} : Multiset α) = {c, d}) : (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hm : a = c ∨ a = d := by
    have hm : a ∈ ({c, d} : Multiset α) := by rw [← h]; simp
    simpa using hm
  rcases hm with rfl | rfl
  · exact Or.inl ⟨rfl, by simpa using h⟩
  · rw [Multiset.pair_comm c a] at h
    exact Or.inr ⟨rfl, by simpa using h⟩

/-- A product of two ciphertexts has exactly the direct and swapped E0 matchings. -/
theorem ciphertext_product_pairing (k r m l s n k' r' m' l' s' n' : Term V)
    (h : BaseEq (.binary .mul (.ternary .penc k r m) (.ternary .penc l s n))
      (.binary .mul (.ternary .penc k' r' m') (.ternary .penc l' s' n'))) :
    (BaseEq (.ternary .penc k r m) (.ternary .penc k' r' m') ∧
      BaseEq (.ternary .penc l s n) (.ternary .penc l' s' n')) ∨
    (BaseEq (.ternary .penc k r m) (.ternary .penc l' s' n') ∧
      BaseEq (.ternary .penc l s n) (.ternary .penc k' r' m')) := by
  have he := h.mul_factors
  simp only [Term.mulFactors, Multiset.singleton_add] at he
  rcases pair_matching he with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl ⟨(baseClass_eq_iff _ _).mp ha, (baseClass_eq_iff _ _).mp hb⟩
  · exact Or.inr ⟨(baseClass_eq_iff _ _).mp ha, (baseClass_eq_iff _ _).mp hb⟩

/-- Same-position E7 root overlaps for arbitrary E0-equivalent left sides. -/
theorem homomorphic_root_outputs_base (k r s m n k' r' s' m' n' : Term V)
    (h : BaseEq (.binary .mul (.ternary .penc k r m) (.ternary .penc k s n))
      (.binary .mul (.ternary .penc k' r' m') (.ternary .penc k' s' n'))) :
    BaseEq (.ternary .penc k (.binary .compose r s) (.binary .add m n))
      (.ternary .penc k' (.binary .compose r' s') (.binary .add m' n')) := by
  rcases ciphertext_product_pairing _ _ _ _ _ _ _ _ _ _ _ _ h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨hk, hr, hm⟩ := (BaseEq.penc_iff _ _ _ _ _ _).mp ha
    obtain ⟨_, hs, hn⟩ := (BaseEq.penc_iff _ _ _ _ _ _).mp hb
    exact .ternary .penc hk (.binary .compose hr hs) (.binary .add hm hn)
  · obtain ⟨hk, hr, hm⟩ := (BaseEq.penc_iff _ _ _ _ _ _).mp ha
    obtain ⟨_, hs, hn⟩ := (BaseEq.penc_iff _ _ _ _ _ _).mp hb
    exact .ternary .penc hk
      ((BaseEq.binary .compose hr hs).trans (.equation (.comm .compose trivial _ _)))
      ((BaseEq.binary .add hm hn).trans (.equation (.comm .add trivial _ _)))

/-- All pairs of root-rule instances, modulo arbitrary E0 equality of their sources.
This does not classify redex positions inside larger contexts. -/
theorem root_outputs_base {a b a' b' : Term V}
    (ha : RootStep a b) (hb : RootStep a' b') (he : BaseEq a a') : BaseEq b b' := by
  by_cases hrigid : a.headTag ≠ .binary .mul
  · exact rigid_root_outputs_base ha hb he hrigid
  · cases ha <;> simp [Term.headTag] at hrigid
    cases hb <;> first
      | exact homomorphic_root_outputs_base _ _ _ _ _ _ _ _ _ _ he
      | exact False.elim (by have hh := he.head_eq; simp [Term.headTag] at hh)

theorem root_peak_joined {a b a' b' : Term V}
    (ha : RootStep a b) (hb : RootStep a' b') (he : BaseEq a a') :
    ModuloStep a b ∧ ModuloStep a b' ∧ JoinModulo b b' :=
  ⟨ha.to_modulo, hb.to_modulo.pre_base he, ⟨b', .base (root_outputs_base ha hb he), .refl _⟩⟩

namespace HomomorphicRootSPOT

abbrev leftCipher : Term Nat := .ternary .penc (.name 0) (.name 1) (.const .zero)
abbrev rightCipher : Term Nat := .ternary .penc (.name 0) (.name 2) (.const .one)
abbrev leftResult : Term Nat := .ternary .penc (.name 0)
  (.binary .compose (.name 1) (.name 2)) (.binary .add (.const .zero) (.const .one))
abbrev rightResult : Term Nat := .ternary .penc (.name 0)
  (.binary .compose (.name 2) (.name 1)) (.binary .add (.const .one) (.const .zero))

/-- Hand-derived E7/AC routes join, while their nonce order distinguishes raw syntax. -/
theorem swapped_ciphertexts_join :
    ModuloStep (.binary .mul leftCipher rightCipher) leftResult ∧
    ModuloStep (.binary .mul leftCipher rightCipher) rightResult ∧
    JoinModulo leftResult rightResult ∧ leftResult ≠ rightResult := by
  have h := root_peak_joined
    (RootStep.homomorphic (.name 0) (.name 1) (.name 2) (.const .zero) (.const .one))
    (RootStep.homomorphic (.name 0) (.name 2) (.name 1) (.const .one) (.const .zero))
    (BaseEq.equation (.comm .mul trivial leftCipher rightCipher))
  exact ⟨h.1, h.2.1, h.2.2, by decide⟩

/-- The unordered quotient does not identify different factor atoms. -/
theorem ordered_factors_not_invariant :
    BaseEq (Term.binary .mul (.name 0) (.name 1)) (.binary .mul (.name 1) (.name 0) : Term Nat) ∧
    [(Term.name 0 : Term Nat).baseClass, (Term.name 1 : Term Nat).baseClass] ≠
      [(Term.name 1 : Term Nat).baseClass, (Term.name 0 : Term Nat).baseClass] := by
  refine ⟨.equation (.comm .mul trivial _ _), ?_⟩
  intro he
  have hfirst := (List.cons.inj he).1
  have hn := (BaseEq.name_iff (V := Nat) 0 1).mp ((baseClass_eq_iff _ _).mp hfirst)
  omega

end HomomorphicRootSPOT
end ExplainableCrypto.Helios.Symbolic
