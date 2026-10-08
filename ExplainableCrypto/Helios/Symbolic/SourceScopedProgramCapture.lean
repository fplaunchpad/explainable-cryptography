import ExplainableCrypto.Helios.Symbolic.SourceTermProgramCapture
import ExplainableCrypto.Helios.Symbolic.SourceScopedTermProgram
import ExplainableCrypto.Helios.Symbolic.SourceNamePrefixPolicies

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.ScopedTermProgram

/-- Actual raw output target with each original local and base-name scope
retained. This extends the target description to the existing scoped syntax. -/
def capture : {V : Type} → ScopedTermProgram V → Named (Option V)
  | _, .result m => .embed (Extended.capture m .nil)
  | _, .letTerm m p => .newVar
      ((Named.par ((Named.embed (.active none (shiftTerm m))).rename some) p.capture).rename Extended.swapBinders)
  | _, .newName n p => .newName (.base n) p.capture

variable {V : Type}

/-- Every original name/variable Scope produces this exact target, even when
hoisting is unavailable. Base-name scopes do not hide the static channel. -/
theorem compile_output_capture (p : ScopedTermProgram V) (c : Nat) :
    Named.BoundOutput (p.compile c) c p.capture := by
  induction p with
  | result m => exact .embed (Extended.message_output c m .nil)
  | letTerm m p ih => exact .scopeVar (.parRight _ ih)
  | newName n p ih => exact .scopeName _ (by intro h; cases h) ih

/-- The existing provider-freshness condition also hoists the actual output
target, after each required variable exchange. All binders remain explicit. -/
theorem capture_hoist (p : ScopedTermProgram V) (hp : p.Hoistable) :
    Named.Structural p.capture
      (Named.restrictNames (p.names.map SourceName.base) (.embed p.erase.capture)) := by
  induction p with
  | result => exact .refl _
  | newName n p ih => exact .newName (.base n) (ih hp)
  | letTerm m p ih =>
    let a := (Named.embed (Extended.active none (shiftTerm m))).rename some
    have hf : ∀ u ∈ p.names.map SourceName.base, u ∉ a.freeNames := by
      intro u hu
      obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hu
      simpa only [a,Named.freeNames_rename,Named.freeNames,Extended.nameSupport,
        shiftTerm,Term.nameSupport_rename,Finset.mem_image,SourceName.base.injEq,exists_eq_right] using hp.2 n hn
    have hs := ((Named.Structural.parRight a (ih hp.1)).trans
      (Named.Structural.par_restrictNames_right a _ _ hf)).rename
        Extended.swapBinders Extended.swapBinders_involutive.injective
    rw [Named.restrictNames_rename] at hs
    have pack := (Named.Structural.newVar
      ((Named.Structural.embedPar ((Extended.active none (shiftTerm m)).rename some) p.erase.capture).symm.rename
        Extended.swapBinders Extended.swapBinders_involutive.injective)).trans
      (Named.Structural.embedVar _).symm
    exact (Named.Structural.newVar hs).trans
      ((Named.Structural.var_restrictNames _ _).trans (pack.restrictNames _))

/-- Only after the actual capture scopes have been retained and safely hoisted
are the dependent locals eliminated to the complete computed value. -/
theorem capture_normalizes (p : ScopedTermProgram V) (hp : p.Hoistable) :
    Named.Structural p.capture
      (Named.restrictNames (p.names.map SourceName.base) (.embed (Extended.capture p.erase.value .nil))) :=
  (p.capture_hoist hp).trans ((Named.Structural.embed p.erase.capture_normalizes).restrictNames _)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.ScopedTermProgram
