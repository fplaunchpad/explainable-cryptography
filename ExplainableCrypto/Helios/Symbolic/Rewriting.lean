import ExplainableCrypto.Helios.Symbolic.RewriteMeasure
import Mathlib.Order.RelClasses
import Lean.Elab.Tactic.Omega

/-! Appendix B.2.2's oriented rules modulo its background theory E0.
Termination and existence below do not assert confluence or a unique normal form. -/
namespace ExplainableCrypto.Helios.Symbolic

inductive BaseEquation {V : Type} : Term V → Term V → Prop where
  | zero_one : BaseEquation (.binary .add (.const .zero) (.const .one)) (.const .one)
  | zero_zero : BaseEquation (.binary .add (.const .zero) (.const .zero)) (.const .zero)
  | comm (f) (h : AC f) (a b) : BaseEquation (.binary f a b) (.binary f b a)
  | assoc (f) (h : AC f) (a b c) : BaseEquation
      (.binary f (.binary f a b) c) (.binary f a (.binary f b c))

/-- Congruence closure of E0, not all of E. -/
inductive BaseEq {V : Type} : Term V → Term V → Prop where
  | equation {a b} : BaseEquation a b → BaseEq a b
  | refl (a) : BaseEq a a
  | symm {a b} : BaseEq a b → BaseEq b a
  | trans {a b c} : BaseEq a b → BaseEq b c → BaseEq a c
  | unary (f) {a b} : BaseEq a b → BaseEq (.unary f a) (.unary f b)
  | binary (f) {a a' b b'} : BaseEq a a' → BaseEq b b' →
      BaseEq (.binary f a b) (.binary f a' b')
  | ternary (f) {a a' b b' c c'} : BaseEq a a' → BaseEq b b' → BaseEq c c' →
      BaseEq (.ternary f a b c) (.ternary f a' b' c')
  | spk {a a' b b' c c' d d'} : BaseEq a a' → BaseEq b b' → BaseEq c c' → BaseEq d d' →
      BaseEq (.spk a b c d) (.spk a' b' c' d')

/-- The seven oriented rule schemata E1, E2 and E5–E9. -/
inductive RootStep {V : Type} : Term V → Term V → Prop where
  | fst (x y) : RootStep (.unary .fst (.binary .pair x y)) x
  | snd (x y) : RootStep (.unary .snd (.binary .pair x y)) y
  | decrypt (k r m) : RootStep
      (.binary .dec k (.ternary .penc (.unary .pk k) r m)) m
  | partial_decrypt (k r m) : RootStep
      (.binary .dec (.binary .partialDecrypt k (.ternary .penc (.unary .pk k) r m))
        (.ternary .penc (.unary .pk k) r m)) m
  | homomorphic (k r s m n) : RootStep
      (.binary .mul (.ternary .penc k r m) (.ternary .penc k s n))
      (.ternary .penc k (.binary .compose r s) (.binary .add m n))
  | check_zero (k r) : RootStep
      (.ternary .checkspk k (.ternary .penc k r (.const .zero))
        (.spk k r (.const .zero) (.ternary .penc k r (.const .zero)))) (.const .ok)
  | check_one (k r) : RootStep
      (.ternary .checkspk k (.ternary .penc k r (.const .one))
        (.spk k r (.const .one) (.ternary .penc k r (.const .one)))) (.const .ok)

/-- The split covers the entire source theory's generating equations. -/
theorem Equation.classify {V : Type} {a b : Term V} (h : Equation a b) :
    BaseEquation a b ∨ RootStep a b := by
  cases h <;> first
    | exact Or.inl (by constructor; assumption)
    | exact Or.inl (by constructor)
    | exact Or.inr (by constructor)


/-- A single hole in any argument position of the entire fixed-arity signature. -/
inductive Context (V : Type) where
  | hole
  | unary : Unary → Context V → Context V
  | binaryLeft : Binary → Context V → Term V → Context V
  | binaryRight : Binary → Term V → Context V → Context V
  | ternaryFirst : Ternary → Context V → Term V → Term V → Context V
  | ternarySecond : Ternary → Term V → Context V → Term V → Context V
  | ternaryThird : Ternary → Term V → Term V → Context V → Context V
  | spkFirst : Context V → Term V → Term V → Term V → Context V
  | spkSecond : Term V → Context V → Term V → Term V → Context V
  | spkThird : Term V → Term V → Context V → Term V → Context V
  | spkFourth : Term V → Term V → Term V → Context V → Context V

namespace Context
variable {V : Type}

def fill (c : Context V) (t : Term V) : Term V :=
  match c with
  | .hole => t
  | .unary f c => .unary f (c.fill t)
  | .binaryLeft f c b => .binary f (c.fill t) b
  | .binaryRight f a c => .binary f a (c.fill t)
  | .ternaryFirst f c b d => .ternary f (c.fill t) b d
  | .ternarySecond f a c d => .ternary f a (c.fill t) d
  | .ternaryThird f a b c => .ternary f a b (c.fill t)
  | .spkFirst c b d e => .spk (c.fill t) b d e
  | .spkSecond a c d e => .spk a (c.fill t) d e
  | .spkThird a b c e => .spk a b (c.fill t) e
  | .spkFourth a b d c => .spk a b d (c.fill t)

theorem weight_fill (c : Context V) (t : Term V) :
    (c.fill t).cryptoWeight = (c.fill (.const .zero)).cryptoWeight + t.cryptoWeight := by
  induction c <;> simp_all [fill, Term.cryptoWeight] <;> omega

theorem congr {a b : Term V} (c : Context V) (h : EqE a b) : EqE (c.fill a) (c.fill b) := by
  induction c with
  | hole => exact h
  | unary f c ih => exact .unary f ih
  | binaryLeft f c b ih => exact .binary f ih (.refl _)
  | binaryRight f a c ih => exact .binary f (.refl _) ih
  | ternaryFirst f c b d ih => exact .ternary f ih (.refl _) (.refl _)
  | ternarySecond f a c d ih => exact .ternary f (.refl _) ih (.refl _)
  | ternaryThird f a b c ih => exact .ternary f (.refl _) (.refl _) ih
  | spkFirst c b d e ih => exact .spk ih (.refl _) (.refl _) (.refl _)
  | spkSecond a c d e ih => exact .spk (.refl _) ih (.refl _) (.refl _)
  | spkThird a b c e ih => exact .spk (.refl _) (.refl _) ih (.refl _)
  | spkFourth a b d c ih => exact .spk (.refl _) (.refl _) (.refl _) ih

end Context
variable {V : Type}

def RewriteStep (a b : Term V) : Prop :=
  ∃ (c : Context V) (l r : Term V), RootStep l r ∧ a = c.fill l ∧ b = c.fill r

def ModuloStep (a b : Term V) : Prop :=
  ∃ a' b', BaseEq a a' ∧ RewriteStep a' b' ∧ BaseEq b' b

theorem BaseEquation.weight_eq {a b : Term V} (h : BaseEquation a b) :
    a.cryptoWeight = b.cryptoWeight := by
  cases h <;> simp only [Term.cryptoWeight] <;> omega

theorem BaseEq.weight_eq {a b : Term V} (h : BaseEq a b) :
    a.cryptoWeight = b.cryptoWeight := by
  induction h with
  | equation h => exact h.weight_eq
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | unary _ _ ih => simp only [Term.cryptoWeight, ih]
  | binary _ _ _ ih₁ ih₂ => simp only [Term.cryptoWeight, ih₁, ih₂]
  | ternary _ _ _ _ ih₁ ih₂ ih₃ => simp only [Term.cryptoWeight, ih₁, ih₂, ih₃]
  | spk _ _ _ _ ih₁ ih₂ ih₃ ih₄ => simp only [Term.cryptoWeight, ih₁, ih₂, ih₃, ih₄]

theorem RootStep.weight_lt {a b : Term V} (h : RootStep a b) :
    b.cryptoWeight < a.cryptoWeight := by
  cases h <;> simp only [Term.cryptoWeight] <;> omega

theorem RewriteStep.weight_lt {a b : Term V} (h : RewriteStep a b) :
    b.cryptoWeight < a.cryptoWeight := by
  obtain ⟨c, l, r, h, rfl, rfl⟩ := h
  rw [c.weight_fill r, c.weight_fill l]
  exact Nat.add_lt_add_left h.weight_lt _

theorem ModuloStep.weight_lt {a b : Term V} (h : ModuloStep a b) :
    b.cryptoWeight < a.cryptoWeight := by
  obtain ⟨a', b', ha, h, hb⟩ := h
  rw [ha.weight_eq, ← hb.weight_eq]
  exact h.weight_lt

theorem BaseEquation.sound {a b : Term V} (h : BaseEquation a b) : EqE a b := by
  cases h with
  | zero_one => exact .equation .zero_one
  | zero_zero => exact .equation .zero_zero
  | comm f h a b => exact .equation (.comm f h a b)
  | assoc f h a b c => exact .equation (.assoc f h a b c)

theorem BaseEq.sound {a b : Term V} (h : BaseEq a b) : EqE a b := by
  induction h with
  | equation h => exact h.sound
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | unary f _ ih => exact .unary f ih
  | binary f _ _ ih₁ ih₂ => exact .binary f ih₁ ih₂
  | ternary f _ _ _ ih₁ ih₂ ih₃ => exact .ternary f ih₁ ih₂ ih₃
  | spk _ _ _ _ ih₁ ih₂ ih₃ ih₄ => exact .spk ih₁ ih₂ ih₃ ih₄

theorem RootStep.sound {a b : Term V} (h : RootStep a b) : EqE a b := by
  apply EqE.equation
  cases h <;> constructor

theorem RewriteStep.sound {a b : Term V} (h : RewriteStep a b) : EqE a b := by
  obtain ⟨c, l, r, h, rfl, rfl⟩ := h
  exact c.congr h.sound

theorem ModuloStep.sound {a b : Term V} (h : ModuloStep a b) : EqE a b := by
  obtain ⟨a', b', ha, h, hb⟩ := h
  exact ha.sound.trans (h.sound.trans hb.sound)

/-- Reverse orientation is required by Lean's well-founded relation convention. -/
theorem rewrite_wellFounded : WellFounded (fun b a : Term V => ModuloStep a b) :=
  Subrelation.wf (fun h => h.weight_lt) (measure Term.cryptoWeight).wf

abbrev Reduces (a b : Term V) := Relation.ReflTransGen ModuloStep a b

def Irreducible (a : Term V) : Prop := ∀ b, ¬ ModuloStep a b

/-- Existence only: there is no uniqueness or algorithm claim here. -/
theorem exists_normal_form (a : Term V) : ∃ b, Reduces a b ∧ Irreducible b := by
  classical
  induction a using rewrite_wellFounded.induction with
  | h a ih =>
    by_cases hn : ∃ b, ModuloStep a b
    · obtain ⟨b, hab⟩ := hn
      obtain ⟨c, hbc, hc⟩ := ih b hab
      exact ⟨c, .head hab hbc, hc⟩
    · exact ⟨a, .refl, fun b hb => hn ⟨b, hb⟩⟩

theorem Reduces.sound {a b : Term V} (h : Reduces a b) : EqE a b := by
  induction h with
  | refl => exact .refl _
  | tail _ h ih => exact ih.trans h.sound

/-- Canonicality still requires confluence; this states just reachable E-equivalence. -/
theorem exists_equivalent_normal_form (a : Term V) :
    ∃ b, Reduces a b ∧ EqE a b ∧ Irreducible b := by
  obtain ⟨b, h, hn⟩ := exists_normal_form a
  exact ⟨b, h, h.sound, hn⟩

end ExplainableCrypto.Helios.Symbolic
