import ExplainableCrypto.Helios.Symbolic.SourceGuardedProgram

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.GuardedProgram
variable {V : Type}

/-- A real free input exposes the substituted continuation's head lets. -/
theorem receives (c : Nat) (m : Term V) (p : GuardedProgram (Option V)) :
    Extended.FreeStep (input c p).expand (.input c m)
      (p.subst (inputSubst m)).expand := by
  have h := (p.subst (inputSubst m)).expand_normalizes.symm
  rw [inline_subst] at h
  exact .congr (.refl _) (.input c m p.inline) h

/-- Communication preserves the sender continuation and activates the receiver. -/
theorem communicates (c : Nat) (m : Term V) (sender : Agent V)
    (p : GuardedProgram (Option V)) :
    Extended.Reduction (.par (.plain (.output c m sender)) (input c p).expand)
      (.par (.plain sender) (p.subst (inputSubst m)).expand) := by
  have h := (p.subst (inputSubst m)).expand_normalizes.symm
  rw [inline_subst] at h
  exact .congr (Extended.Structural.plainPar _ _).symm
    (Extended.message_communication c m sender p.inline)
    ((Extended.Structural.plainPar _ _).trans (Extended.Structural.parRight _ h))

theorem selects_then (f : Formula Empty) (p q : GuardedProgram Empty) (hf : f.Holds Empty.elim) :
    Extended.Reduction (branch f p q).expand p.expand :=
  .congr (.refl _) (Extended.coreStep_derivable (.thenBranch f p.inline q.inline hf))
    p.expand_normalizes.symm

theorem selects_else (f : Formula Empty) (p q : GuardedProgram Empty) (hf : ¬ f.Holds Empty.elim) :
    Extended.Reduction (branch f p q).expand q.expand :=
  .congr (.refl _) (Extended.coreStep_derivable (.elseBranch f p.inline q.inline hf))
    q.expand_normalizes.symm

/-- Out-Atom/Open-Atom capture the complete payload in a new public variable.
The remaining construction shifts past that export before its head lets expand. -/
theorem publishes (c : Nat) (m : Term V) (p : GuardedProgram V) :
    Extended.BoundOutput (output c m p).expand c
      (.par (.active none (shiftTerm m)) (p.subst (fun v => .var (some v))).expand) := by
  have h := (p.subst (fun v => Term.var (some v))).expand_normalizes.symm
  rw [inline_subst] at h
  exact .congr (.refl _) (Extended.message_output c m p.inline)
    (Extended.Structural.parRight _ h)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.GuardedProgram
