import ExplainableCrypto.Helios.Symbolic.Terms

namespace ExplainableCrypto.Helios.Symbolic
open Term

/-- The three AC operations. No unit laws are added. -/
def AC : Binary → Prop
  | .mul | .add | .compose => True
  | _ => False

/-- Generating equations E1–E9 and AC, universally instantiated at terms. -/
inductive Equation {V : Type} : Term V → Term V → Prop where
  | fst (x y) : Equation (.unary .fst (.binary .pair x y)) x
  | snd (x y) : Equation (.unary .snd (.binary .pair x y)) y
  | zero_one : Equation (.binary .add (.const .zero) (.const .one)) (.const .one)
  | zero_zero : Equation (.binary .add (.const .zero) (.const .zero)) (.const .zero)
  | decrypt (k r m) : Equation
      (.binary .dec k (.ternary .penc (.unary .pk k) r m)) m
  | partial_decrypt (k r m) : Equation
      (.binary .dec (.binary .partialDecrypt k (.ternary .penc (.unary .pk k) r m))
        (.ternary .penc (.unary .pk k) r m)) m
  | homomorphic (k r s m n) : Equation
      (.binary .mul (.ternary .penc k r m) (.ternary .penc k s n))
      (.ternary .penc k (.binary .compose r s) (.binary .add m n))
  | check_zero (k r) : Equation
      (.ternary .checkspk k (.ternary .penc k r (.const .zero))
        (.spk k r (.const .zero) (.ternary .penc k r (.const .zero)))) (.const .ok)
  | check_one (k r) : Equation
      (.ternary .checkspk k (.ternary .penc k r (.const .one))
        (.spk k r (.const .one) (.ternary .penc k r (.const .one)))) (.const .ok)
  | comm (f) (h : AC f) (a b) : Equation (.binary f a b) (.binary f b a)
  | assoc (f) (h : AC f) (a b c) : Equation
      (.binary f (.binary f a b) c) (.binary f a (.binary f b c))

/-- Equality modulo the source theory, defined as a congruence closure. -/
inductive EqE {V : Type} : Term V → Term V → Prop where
  | equation {a b} : Equation a b → EqE a b
  | refl (a) : EqE a a
  | symm {a b} : EqE a b → EqE b a
  | trans {a b c} : EqE a b → EqE b c → EqE a c
  | unary (f) {a b} : EqE a b → EqE (.unary f a) (.unary f b)
  | binary (f) {a a' b b'} : EqE a a' → EqE b b' →
      EqE (.binary f a b) (.binary f a' b')
  | ternary (f) {a a' b b' c c'} : EqE a a' → EqE b b' → EqE c c' →
      EqE (.ternary f a b c) (.ternary f a' b' c')
  | spk {a a' b b' c c' d d'} : EqE a a' → EqE b b' → EqE c c' → EqE d d' →
      EqE (.spk a b c d) (.spk a' b' c' d')

variable {V W : Type}

theorem Equation.subst {a b : Term V} (h : Equation a b) (σ : V → Term W) :
    Equation (a.subst σ) (b.subst σ) := by
  cases h <;> simp only [Term.subst] <;> constructor <;> assumption

theorem EqE.subst {a b : Term V} (h : EqE a b) (σ : V → Term W) :
    EqE (a.subst σ) (b.subst σ) := by
  induction h with
  | equation h => exact .equation (h.subst σ)
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | unary f _ ih => exact .unary f ih
  | binary f _ _ ih₁ ih₂ => exact .binary f ih₁ ih₂
  | ternary f _ _ _ ih₁ ih₂ ih₃ => exact .ternary f ih₁ ih₂ ih₃
  | spk _ _ _ _ ih₁ ih₂ ih₃ ih₄ => exact .spk ih₁ ih₂ ih₃ ih₄

/-- Every recipe respects pointwise equational equality of its handle values. -/
theorem Term.subst_congr (r : Term V) (σ τ : V → Term W)
    (h : ∀ v, EqE (σ v) (τ v)) : EqE (r.subst σ) (r.subst τ) := by
  induction r with
  | name => exact .refl _
  | var v => exact h v
  | const => exact .refl _
  | unary f a ih => exact .unary f ih
  | binary f a b ih₁ ih₂ => exact .binary f ih₁ ih₂
  | ternary f a b c ih₁ ih₂ ih₃ => exact .ternary f ih₁ ih₂ ih₃
  | spk a b c d ih₁ ih₂ ih₃ ih₄ => exact .spk ih₁ ih₂ ih₃ ih₄

end ExplainableCrypto.Helios.Symbolic
