import ExplainableCrypto.Helios.Symbolic.SourceRecipeCaptureNormalization

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

/-- Scope's exchange followed by eliminating the old local leaves the exported
None fixed and substitutes the local only through the older Some positions. -/
theorem swap_then_bind_local (m : Term V) :
    (fun v : Option (Option V) => (Term.var (swapBinders v)).subst (inputSubst (shiftTerm m))) =
      liftSubst (inputSubst m) := by
  funext v
  cases v with
  | none => rfl
  | some v => cases v <;> rfl

private theorem scope_provider (m : Term V) :
    ((Extended.active none (shiftTerm m)).rename some).rename swapBinders =
      (.active none (shiftTerm (shiftTerm m)) : Extended (Option (Option V))) := by
  simp only [rename,Term.subst_subst,shiftTerm,swapBinders]
  congr 1

/-- An actual local provider remains eliminable after output's binder exchange.
The complete exported payload and every continuation use are retained. -/
theorem scope_capture_normalize (m : Term V) (r : Term (Option V))
    (p : Agent (Option (Option V))) :
    Structural
      (.newVar ((Extended.par ((Extended.active none (shiftTerm m)).rename some)
        (.par (.active none (shiftTerm r)) (.plain p))).rename swapBinders))
      (.par (.active none (shiftTerm (bindInput r m)))
        (.plain (p.subst (liftSubst (inputSubst m))))) := by
  have he : ((shiftTerm r).subst (fun v => .var (swapBinders v))).subst (inputSubst (shiftTerm m)) =
      shiftTerm (bindInput r m) := by
    rw [Term.subst_subst,swap_then_bind_local,shiftTerm_subst]
    rfl
  have hp : (p.subst (fun v => .var (swapBinders v))).subst (inputSubst (shiftTerm m)) =
      p.subst (liftSubst (inputSubst m)) := by
    rw [Agent.subst_subst,swap_then_bind_local]
  have hi : Instantiates (inputSubst (shiftTerm m))
      ((Extended.par (.active none (shiftTerm r)) (.plain p)).rename swapBinders)
      (.par (.active none (shiftTerm (bindInput r m)))
        (.plain (p.subst (liftSubst (inputSubst m))))) := by
    have hg := Instantiates.par
      (Instantiates.active (inputSubst (shiftTerm m)) (some none) none
        ((shiftTerm r).subst (fun v => .var (swapBinders v))) rfl)
      (Instantiates.plain (inputSubst (shiftTerm m)) (p.subst (fun v => .var (swapBinders v))))
    rw [he,hp] at hg
    exact hg
  have hs := Structural.let_normalize (shiftTerm m)
    (by simp [rename,Exports,swapBinders]) hi
  change Structural (.newVar (.par
    (((Extended.active none (shiftTerm m)).rename some).rename swapBinders)
    ((Extended.par (.active none (shiftTerm r)) (.plain p)).rename swapBinders))) _
  rw [scope_provider]
  exact hs

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
