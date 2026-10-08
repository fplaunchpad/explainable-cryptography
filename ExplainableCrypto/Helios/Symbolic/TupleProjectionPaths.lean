import ExplainableCrypto.Helios.Symbolic.ProjectionInversion
import ExplainableCrypto.Helios.Symbolic.Ballot

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

theorem Term.drop_succ_outer (n : Nat) (t : Term V) :
    t.drop (n + 1) = .unary .snd (t.drop n) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => simpa only [Term.drop] using ih (.unary .snd t)

theorem ReducesModulo.drop {a b : Term V} (h : ReducesModulo a b) (n : Nat) :
    ReducesModulo (a.drop n) (b.drop n) := by
  induction n generalizing a b with
  | zero => exact h
  | succ n ih => exact ih (h.context (.unary .snd .hole))

/-- A valid tuple tail is reached by actual selector steps, even with reducible fields. -/
theorem tuple_drop_reduces (xs : List (Term V)) (n : Nat) (hn : n ≤ xs.length) :
    ReducesModulo ((Term.tuple xs).drop n) (Term.tuple (xs.drop n)) := by
  induction xs generalizing n with
  | nil =>
    have : n = 0 := by simpa using hn
    subst n
    exact .refl _
  | cons x xs ih =>
    cases n with
    | zero => exact .refl _
    | succ n =>
      exact ((ReducesModulo.single (RootStep.snd x (Term.tuple xs)).to_modulo).drop n).trans
        (ih n (by simpa using hn))

theorem tuple_eqE_pair_nonempty (xs : List (Term V)) {x y : Term V}
    (h : EqE (Term.tuple xs) (.binary .pair x y)) : 0 < xs.length := by
  cases xs with
  | nil =>
    obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp h
    obtain ⟨_, _, hp, _⟩ := hr.passive_binary_components (Or.inl rfl)
    cases (((constant_irreducible .bottom).reducesModulo hl).trans hp).head_eq
  | cons => simp

theorem tuple_not_eqE_penc (xs : List (Term V)) (k r m : Term V) :
    ¬ EqE (Term.tuple xs) (.ternary .penc k r m) := by
  cases xs with
  | nil =>
    intro h
    obtain ⟨_, _, _, he, _⟩ := h.symm.penc_irreducible_shape (constant_irreducible .bottom)
    cases he
  | cons a xs => exact fun h => penc_not_eqE_passive_binary .pair (Or.inl rfl) _ _ _ _ _ h.symm

theorem tuple_not_eqE_spk (xs : List (Term V)) (k r m c : Term V) :
    ¬ EqE (Term.tuple xs) (.spk k r m c) := by
  cases xs with
  | nil =>
    intro h
    obtain ⟨_, _, _, _, he, _⟩ := h.symm.spk_irreducible_shape (constant_irreducible .bottom)
    cases he
  | cons a xs => exact fun h => spk_not_eqE_passive_binary .pair (Or.inl rfl) _ _ _ _ _ _ h.symm

end ExplainableCrypto.Helios.Symbolic
