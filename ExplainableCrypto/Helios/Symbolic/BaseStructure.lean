import ExplainableCrypto.Helios.Symbolic.Rewriting

/-! Metatheory observations for E0. These functions are not new term constructors
or public-recipe destructors; in particular, rigidArgument does not grant an
attacker access to ciphertext arguments. -/
namespace ExplainableCrypto.Helios.Symbolic

/-- The zero/one/addition class shares one tag because E3 and E4 change its root.
All other tags retain the exact symbol (and atom identity). -/
inductive HeadTag (V : Type) where
  | name : Nat → HeadTag V
  | var : V → HeadTag V
  | const : Constant → HeadTag V
  | sum
  | unary : Unary → HeadTag V
  | binary : Binary → HeadTag V
  | ternary : Ternary → HeadTag V
  | spk
  deriving DecidableEq, Repr

def Term.headTag {V : Type} : Term V → HeadTag V
  | .name n => .name n
  | .var v => .var v
  | .const .zero | .const .one => .sum
  | .const c => .const c
  | .unary f _ => .unary f
  | .binary .add _ _ => .sum
  | .binary f _ _ => .binary f
  | .ternary f _ _ _ => .ternary f
  | .spk _ _ _ _ => .spk

/-- Observe only fixed argument positions. AC arguments are deliberately opaque;
the default bottom does not assert that an absent argument is a protocol value. -/
def Term.rigidArgument {V : Type} (i : Nat) : Term V → Term V
  | .unary _ a => if i = 0 then a else .const .bottom
  | .binary f a b => match f with
    | .mul | .add | .compose => .const .bottom
    | _ => if i = 0 then a else if i = 1 then b else .const .bottom
  | .ternary _ a b c => if i = 0 then a else if i = 1 then b else if i = 2 then c else .const .bottom
  | .spk a b c d => if i = 0 then a else if i = 1 then b else if i = 2 then c else
      if i = 3 then d else .const .bottom
  | _ => .const .bottom

variable {V : Type}

theorem BaseEquation.head_eq {a b : Term V} (h : BaseEquation a b) :
    a.headTag = b.headTag := by
  cases h with
  | zero_one => rfl
  | zero_zero => rfl
  | comm f _ => cases f <;> rfl
  | assoc f _ => cases f <;> rfl

theorem BaseEq.head_eq {a b : Term V} (h : BaseEq a b) :
    a.headTag = b.headTag := by
  induction h with
  | equation h => exact h.head_eq
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | unary => rfl
  | binary f => cases f <;> rfl
  | ternary => rfl
  | spk => rfl

theorem BaseEquation.argument {a b : Term V} (h : BaseEquation a b) (i : Nat) :
    BaseEq (a.rigidArgument i) (b.rigidArgument i) := by
  cases h with
  | zero_one => exact .refl _
  | zero_zero => exact .refl _
  | comm f hf => cases f <;> simp_all [AC, Term.rigidArgument, BaseEq.refl]
  | assoc f hf => cases f <;> simp_all [AC, Term.rigidArgument, BaseEq.refl]

/-- Rigid argument extraction respects E0, without a confluence hypothesis. -/
theorem BaseEq.argument {a b : Term V} (h : BaseEq a b) (i : Nat) :
    BaseEq (a.rigidArgument i) (b.rigidArgument i) := by
  induction h with
  | equation h => exact h.argument i
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | unary f h ih =>
    rcases i with _ | i <;> simp_all [Term.rigidArgument, BaseEq.refl]
  | binary f ha hb ih₁ ih₂ =>
    cases f <;> rcases i with _ | (_ | i) <;>
      simp_all [Term.rigidArgument, BaseEq.refl]
  | ternary f ha hb hc ih₁ ih₂ ih₃ =>
    rcases i with _ | (_ | (_ | i)) <;> simp_all [Term.rigidArgument, BaseEq.refl]
  | spk ha hb hc hd ih₁ ih₂ ih₃ ih₄ =>
    rcases i with _ | (_ | (_ | (_ | i))) <;> simp_all [Term.rigidArgument, BaseEq.refl]

theorem BaseEq.unary_iff (f g : Unary) (a b : Term V) :
    BaseEq (.unary f a) (.unary g b) ↔ f = g ∧ BaseEq a b := by
  constructor
  · intro h
    have hf := h.head_eq
    simp only [Term.headTag, HeadTag.unary.injEq] at hf
    exact ⟨hf, by simpa [Term.rigidArgument] using h.argument 0⟩
  · rintro ⟨rfl, h⟩
    exact .unary _ h

/-- Pairing, decryption and partial decryption have fixed argument order. -/
theorem BaseEq.binary_iff (f g : Binary) (hf : ¬ AC f) (hg : ¬ AC g)
    (a b c d : Term V) :
    BaseEq (.binary f a b) (.binary g c d) ↔ f = g ∧ BaseEq a c ∧ BaseEq b d := by
  constructor
  · intro h
    have hhead := h.head_eq
    have h₀ := h.argument 0
    have h₁ := h.argument 1
    cases f <;> cases g <;> simp_all [AC, Term.headTag, Term.rigidArgument]
  · rintro ⟨rfl, ha, hb⟩
    exact .binary _ ha hb

theorem BaseEq.ternary_iff (f g : Ternary) (a b c d e f' : Term V) :
    BaseEq (.ternary f a b c) (.ternary g d e f') ↔
      f = g ∧ BaseEq a d ∧ BaseEq b e ∧ BaseEq c f' := by
  constructor
  · intro h
    have hf := h.head_eq
    simp only [Term.headTag, HeadTag.ternary.injEq] at hf
    exact ⟨hf, by simpa [Term.rigidArgument] using h.argument 0,
      by simpa [Term.rigidArgument] using h.argument 1,
      by simpa [Term.rigidArgument] using h.argument 2⟩
  · rintro ⟨rfl, ha, hb, hc⟩
    exact .ternary _ ha hb hc

theorem BaseEq.spk_iff (a b c d a' b' c' d' : Term V) :
    BaseEq (.spk a b c d) (.spk a' b' c' d') ↔
      BaseEq a a' ∧ BaseEq b b' ∧ BaseEq c c' ∧ BaseEq d d' := by
  constructor
  · intro h
    exact ⟨by simpa [Term.rigidArgument] using h.argument 0,
      by simpa [Term.rigidArgument] using h.argument 1,
      by simpa [Term.rigidArgument] using h.argument 2,
      by simpa [Term.rigidArgument] using h.argument 3⟩
  · rintro ⟨ha, hb, hc, hd⟩
    exact .spk ha hb hc hd

theorem BaseEq.name_iff (n m : Nat) : BaseEq (Term.name (V := V) n) (.name m) ↔ n = m := by
  constructor
  · intro h
    exact HeadTag.name.inj h.head_eq
  · rintro rfl
    exact .refl _

/-- This is E0 constructor injectivity, not yet injectivity modulo the full E. -/
theorem BaseEq.penc_iff (k r m k' r' m' : Term V) :
    BaseEq (.ternary .penc k r m) (.ternary .penc k' r' m') ↔
      BaseEq k k' ∧ BaseEq r r' ∧ BaseEq m m' := by
  simpa using BaseEq.ternary_iff .penc .penc k r m k' r' m'

theorem penc_not_base_spk (k r m a b c d : Term V) :
    ¬ BaseEq (.ternary .penc k r m) (.spk a b c d) := by
  intro h
  cases h.head_eq

/-- An E0 representative of a ciphertext still has ciphertext shape. -/
theorem BaseEq.penc_shape {k r m t : Term V}
    (h : BaseEq (.ternary .penc k r m) t) :
    ∃ k' r' m', t = .ternary .penc k' r' m' ∧
      BaseEq k k' ∧ BaseEq r r' ∧ BaseEq m m' := by
  have hh := h.head_eq
  cases t with
  | name => cases hh
  | var => cases hh
  | const c => cases c <;> cases hh
  | unary => cases hh
  | binary f => cases f <;> cases hh
  | ternary f k' r' m' =>
    cases f with
    | penc => exact ⟨k', r', m', rfl, (BaseEq.penc_iff _ _ _ _ _ _).mp h⟩
    | checkspk => cases hh
  | spk => cases hh

/-- E5 and E6 cannot both match E0-equivalent instances: that would equate a
key with a partial-decryption term that strictly contains an equivalent key. -/
theorem decrypt_partial_sources_not_base (k r m k' r' m' : Term V) :
    ¬ BaseEq (.binary .dec k (.ternary .penc (.unary .pk k) r m))
      (.binary .dec (.binary .partialDecrypt k' (.ternary .penc (.unary .pk k') r' m'))
        (.ternary .penc (.unary .pk k') r' m')) := by
  intro h
  obtain ⟨_, hk, hc⟩ := (BaseEq.binary_iff .dec .dec (by simp [AC]) (by simp [AC]) _ _ _ _).mp h
  obtain ⟨hpk, _, _⟩ := (BaseEq.penc_iff _ _ _ _ _ _).mp hc
  obtain ⟨_, hkey⟩ := (BaseEq.unary_iff .pk .pk _ _).mp hpk
  have hw := hk.weight_eq
  have hw' := hkey.weight_eq
  simp only [Term.cryptoWeight] at hw
  omega

namespace BaseStructureSPOT

/-- Independently derived AC fixture: only the nonce order changes. -/
theorem ciphertext_nonce_commutes :
    BaseEq (Term.ternary .penc (.name 0) (.binary .compose (.name 1) (.name 2)) (.const .one))
      (.ternary .penc (.name 0) (.binary .compose (.name 2) (.name 1)) (.const .one) : Term Nat) :=
  .ternary .penc (.refl _) (.equation (.comm .compose trivial _ _)) (.refl _)

/-- Multiplication is not a rigid binary constructor. -/
theorem multiplication_not_argument_injective :
    BaseEq (Term.binary .mul (.name 0) (.name 1)) (.binary .mul (.name 1) (.name 0) : Term Nat) ∧
      ¬ BaseEq (Term.name 0 : Term Nat) (.name 1) := by
  refine ⟨.equation (.comm .mul trivial _ _), ?_⟩
  simp [BaseEq.name_iff]

/-- Retain the raw-root counterexample from the executable gate. -/
theorem addition_can_change_root :
    BaseEq (Term.binary .add (.const .zero) (.const .one)) (.const .one : Term Nat) ∧
    (Term.binary .add (.const .zero) (.const .one) : Term Nat) ≠ .const .one :=
  ⟨.equation .zero_one, by decide⟩

end BaseStructureSPOT
end ExplainableCrypto.Helios.Symbolic
