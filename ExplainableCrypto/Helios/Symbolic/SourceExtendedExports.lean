import ExplainableCrypto.Helios.Symbolic.SourceExtendedSyntax

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V W : Type}

/-- Injective variable renaming preserves each exported variable, including
beneath arbitrarily many variable restrictions. -/
theorem rename_exports (a : Extended V) (f : V → W) (hf : Function.Injective f) (v : V) :
    (a.rename f).Exports (f v) ↔ a.Exports v := by
  induction a generalizing W with
  | plain p => rfl
  | par a b ha hb => exact or_congr (ha f hf v) (hb f hf v)
  | active x m => exact hf.eq_iff
  | newVar a ha =>
    simpa only [rename,Exports,Option.map_some] using ha (Option.map f) (Option.map_injective hf) (some v)

/-- Structural laws cannot remove or create an exported active variable. In
particular Alias removes a restricted variable, never an exported handle. -/
theorem Structural.exports {a b : Extended V} (h : Structural a b) (v : V) :
    a.Exports v ↔ b.Exports v := by
  induction h with
  | refl => rfl
  | symm _ ih => exact (ih v).symm
  | trans _ _ ih ih' => exact (ih v).trans (ih' v)
  | parLeft c _ ih => exact or_congr (ih v) Iff.rfl
  | parRight a _ ih => exact or_congr Iff.rfl (ih v)
  | newVar _ ih => exact ih (some v)
  | plainPar => simp [Exports]
  | zero => simp [Exports]
  | assoc => simp [Exports,or_assoc]
  | comm => simp [Exports,or_comm]
  | newPar a b =>
    exact or_congr (rename_exports a some (Option.some_injective _) v).symm Iff.rfl
  | «alias» => simp [Exports]
  | substPlain => simp [Exports]
  | substActive => rfl
  | rewrite => rfl

/-- Internal reduction also preserves all exported variables. Plain processes
cannot consume active frame bindings, and structural closure preserves them. -/
theorem Reduction.exports {a b : Extended V} (h : Reduction a b) (v : V) :
    a.Exports v ↔ b.Exports v := by
  induction h with
  | atomComm => rfl
  | thenBranch => rfl
  | elseBranch => rfl
  | parLeft c _ ih => exact or_congr (ih v) Iff.rfl
  | parRight a _ ih => exact or_congr Iff.rfl (ih v)
  | newVar _ ih => exact ih (some v)
  | congr ha _ hb ih => exact (ha.exports v).trans ((ih v).trans (hb.exports v))

/-- A free active substitution is never structurally equal to a plain process,
regardless of whether that process mentions the exported variable. -/
theorem active_not_plain (x : V) (m : Term V) (p : Agent V) :
    ¬ Structural (.active x m) (.plain p) := by
  intro h
  exact (h.exports x).mp rfl

/-- The same invariant rules out consuming an exported handle by an internal
reduction, even after arbitrary allowed structural rearrangements. -/
theorem active_no_plain_reduction (x : V) (m : Term V) (p : Agent V) :
    ¬ Reduction (.active x m) (.plain p) := by
  intro h
  exact (h.exports x).mp rfl
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
