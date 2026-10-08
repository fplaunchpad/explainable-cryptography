import ExplainableCrypto.Helios.Symbolic.RootReduction

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Kernel backstop for the failed tree-size invariance conjecture. -/
theorem tree_size_not_base_invariant :
    BaseEq (V := Nat) (.binary .add (.const .zero) (.const .zero)) (.const .zero) ∧
    (Term.binary .add (.const .zero) (.const .zero) : Term Nat).nodeCount ≠
      (Term.const .zero : Term Nat).nodeCount := ⟨.equation .zero_zero, by decide⟩

theorem reduction_not_base_equality {a b : Term V} (h : ModuloStep a b) : ¬ BaseEq a b := by
  intro he
  have hl := h.weight_lt
  rw [he.weight_eq] at hl
  exact Nat.lt_irrefl _ hl

theorem zero_weight_irreducible (a : Term V) (h : a.cryptoWeight = 0) : Irreducible a := by
  intro b hab
  have hl := hab.weight_lt
  rw [h] at hl
  exact Nat.not_lt_zero _ hl

theorem constant_irreducible (c : Constant) : Irreducible (V := V) (.const c) :=
  zero_weight_irreducible _ rfl

/-- A real reduction is available, ruling out a vacuous empty rewrite relation. -/
theorem projection_reduces (a b : Term V) :
    ModuloStep (.unary .fst (.binary .pair a b)) a :=
  ⟨_, _, .refl _, ⟨.hole, _, _, .fst a b, rfl, rfl⟩, .refl _⟩

theorem projection_not_irreducible (a b : Term V) :
    ¬ Irreducible (.unary .fst (.binary .pair a b)) :=
  fun h => h a (projection_reduces a b)

/-- A no-match response is not a normal-form certificate: a nested redex remains. -/
def nestedProjection : Term Nat :=
  .unary .pk (.unary .fst (.binary .pair (.name 0) (.name 1)))

theorem nested_root_no_match : (rootReduce nestedProjection).map Subtype.val = none := by decide

theorem nested_still_reduces : ModuloStep nestedProjection (.unary .pk (.name 0)) :=
  ⟨_, _, .refl _, ⟨.unary .pk .hole, _, _, .fst (.name 0) (.name 1), rfl, rfl⟩, .refl _⟩

/-- Wrong-key decryption is not one of the syntactically matched source rules. -/
theorem wrong_key_no_match :
    (rootReduce (Term.binary .dec (.name 0)
      (.ternary .penc (.unary .pk (.name 1)) (.name 2) (.const .one)) : Term Nat)).map Subtype.val = none := by decide

theorem right_key_match :
    (rootReduce (Term.binary .dec (.name 0)
      (.ternary .penc (.unary .pk (.name 0)) (.name 2) (.const .one)) : Term Nat)).map Subtype.val = some (.const .one) := by decide

/-- The two keys are E0-equal but syntactically different. -/
def backgroundRedex : Term Nat :=
  .binary .mul
    (.ternary .penc (.binary .compose (.name 0) (.name 1)) (.name 2) (.const .zero))
    (.ternary .penc (.binary .compose (.name 1) (.name 0)) (.name 3) (.const .one))

def backgroundResult : Term Nat :=
  .ternary .penc (.binary .compose (.name 0) (.name 1))
    (.binary .compose (.name 2) (.name 3)) (.binary .add (.const .zero) (.const .one))

theorem background_root_no_match : (rootReduce backgroundRedex).map Subtype.val = none := by decide

theorem background_still_reduces : ModuloStep backgroundRedex backgroundResult := by
  let k : Term Nat := .binary .compose (.name 0) (.name 1)
  refine ⟨.binary .mul (.ternary .penc k (.name 2) (.const .zero))
      (.ternary .penc k (.name 3) (.const .one)), backgroundResult, ?_, ?_, .refl _⟩
  · exact .binary .mul (.refl _) (.ternary .penc
      (.equation (.comm .compose trivial (.name 1) (.name 0))) (.refl _) (.refl _))
  · exact ⟨.hole, _, _, .homomorphic k (.name 2) (.name 3) (.const .zero) (.const .one), rfl, rfl⟩

end ExplainableCrypto.Helios.Symbolic
