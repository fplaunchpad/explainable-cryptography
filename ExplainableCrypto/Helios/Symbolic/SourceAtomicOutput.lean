import ExplainableCrypto.Helios.Symbolic.SourceAtomicLabels

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

/-- Full payload plus the shifted continuation after a fresh output. -/
def capture (m : Term V) (p : Agent V) : Extended (Option V) :=
  .par (.active none (shiftTerm m)) (.plain p.shift)

/-- Factor an arbitrary term into a local active let, output its variable using
Out-Atom, then export it using Open-Atom. No payload is redacted or normalized. -/
theorem message_output (c : Nat) (m : Term V) (p : Agent V) :
    BoundOutput (.plain (.output c m p)) c (capture m p) := by
  apply BoundOutput.congr (output_factor c m p) ?_ (.refl _)
  exact .openAtom (.parRight _ (.output c none p.shift))

/-- Free input/output labels do not change the exported frame domain. -/
theorem FreeStep.exports {a b : Extended V} {l : FreeLabel V} (h : FreeStep a l b) (v : V) :
    a.Exports v ↔ b.Exports v := by
  induction h with
  | input => rfl
  | output => rfl
  | scopeInput _ ih => exact ih (some v)
  | scopeOutput _ ih => exact ih (some v)
  | parLeft _ _ ih => exact or_congr (ih v) Iff.rfl
  | parRight _ _ ih => exact or_congr Iff.rfl (ih v)
  | congr ha _ hb ih => exact (ha.exports v).trans ((ih v).trans (hb.exports v))

theorem swapBinders_involutive : Function.Involutive (swapBinders (V := V)) := by
  intro v
  cases v with
  | none => rfl
  | some v => cases v <;> rfl

/-- Fresh output preserves every old exported variable even across variable
Scope, Par and arbitrary allowed structural rewrites. -/
theorem BoundOutput.old_exports {a : Extended V} {b : Extended (Option V)} {c : Nat}
    (h : BoundOutput a c b) (v : V) : b.Exports (some v) ↔ a.Exports v := by
  induction h with
  | openAtom h => exact (h.exports (some v)).symm
  | scope h ih =>
    rename_i V' a' b' c'
    have he := rename_exports b' swapBinders swapBinders_involutive.injective (some (some v))
    exact he.trans (ih (some v))
  | parLeft d h ih => exact or_congr (ih v) (rename_exports d some (Option.some_injective _) v)
  | parRight a h ih => exact or_congr (rename_exports a some (Option.some_injective _) v) (ih v)
  | congr ha h hb ih => exact (hb.exports (some v)).symm.trans ((ih v).trans (ha.exports v).symm)

/-- This particular derived output really introduces an active definition for
the fresh variable. Arbitrary raw ill-formed syntax is not presumed closed. -/
theorem capture_exports_iff (m : Term V) (p : Agent V) (v : Option V) :
    (capture m p).Exports v ↔ v=none := by simp [capture,Exports]

/-- An output in parallel with an arbitrary extended frame/context retains
that whole context, with its old variables shifted past the new export. -/
theorem message_output_in_context (a : Extended V) (c : Nat) (m : Term V) (p : Agent V) :
    BoundOutput (.par a (.plain (.output c m p))) c (.par (a.rename some) (capture m p)) :=
  .parRight a (message_output c m p)
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
