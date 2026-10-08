import ExplainableCrypto.Helios.Symbolic.SourceFreshBoundPrenex
import ExplainableCrypto.Helios.Symbolic.SourceOperationalPrenexSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceBoundPrenexSPOT
open Historical General Source Extended

/-- Some transports the whole substitution path without capturing the new None. -/
theorem injective_substitution_transport :
    ((Agent.output 9 (.binary .pair (.var (0 : Fin 2)) (.var 1)) .nil).subst
      (replaceVar 0 (.name 40))).subst (fun v => .var (some v)) =
    ((Agent.output 9 (.binary .pair (.var (0 : Fin 2)) (.var 1)) .nil).subst
      (fun v => .var (some v))).subst (replaceVar (some 0) (.name 40)) :=
  Agent.replaceVar_rename _ _ _ some (Option.some_injective _)

/-- Collapsing two old variables breaks substitution naturality. -/
theorem collapsing_variable_map_rejected :
    ((Agent.output 9 (.var (1 : Fin 2)) .nil).subst (replaceVar 0 (.name 40))).subst
      (fun _ => (.var 0 : Term Nat)) ≠
    ((Agent.output 9 (.var (1 : Fin 2)) .nil).subst (fun _ => (.var 0 : Term Nat))).subst
      (replaceVar 0 (.name 40)) := by
  simp [Agent.subst,replaceVar,Term.subst]

theorem structural_some_transport :
    Structural
      ((Extended.par (.active (0 : Fin 1) (.name 40)) (.plain (.output 9 (.var 0) .nil))).rename some)
      ((Extended.par (.active (0 : Fin 1) (.name 40)) (.plain (.output 9 (.name 40) .nil))).rename some) := by
  simpa [Agent.subst,replaceVar,Term.subst] using
    (Structural.substPlain (0 : Fin 1) (.name 40) (.output 9 (.var 0) .nil)).rename some (Option.some_injective _)

theorem named_alpha_path_keeps_name_support :
    Named.Structural
      ((Named.newName (.base 40) (.embed SourceNameInterpretationSPOT.binding)).rename some)
      ((Named.newName (.base 50) (.embed (SourceNameInterpretationSPOT.binding.mapNames SourceNameInterpretationSPOT.e id))).rename some) :=
  SourceNameInterpretationSPOT.alpha_binding_representative.rename some (Option.some_injective _)

abbrev source : Named (Fin 1) := .newName (.base 40) (.embed SourceVisibleInterpretationSPOT.scopedSource)
abbrev target : Named (Option (Fin 1)) := .newName (.base 40) (.embed SourceVisibleInterpretationSPOT.scopedTarget)

private theorem scoped_output : Named.BoundOutput source 0 target :=
  .scopeName (.base 40) (by decide) (.embed SourceAtomicOutputSPOT.output_crosses_variable_scope)

theorem scoped_bound_common_prefix :
    ∃ (ns : List SourceName) (a : Extended (Fin 1)) (b : Extended (Option (Fin 1))),
      Named.Structural source (Named.restrictNames ns (.embed a)) ∧
      Named.Structural target (Named.restrictNames ns (.embed b)) ∧ Extended.BoundOutput a 0 b ∧
      ∀ n ∈ ns, n ≠ SourceName.channel 0 := scoped_output.prenex

theorem scoped_bound_reconstructed : Named.BoundOutput source 0 target :=
  (Named.boundOutput_iff_prenex source target 0).mpr scoped_bound_common_prefix

theorem scoped_bound_distinct_fresh :
    ∃ (ns : List SourceName) (a : Extended (Fin 1)) (b : Extended (Option (Fin 1))),
      Named.Structural source (Named.restrictNames ns (.embed a)) ∧
      Named.Structural target (Named.restrictNames ns (.embed b)) ∧ Extended.BoundOutput a 0 b ∧
      ns.Nodup ∧ ∀ n ∈ ns, n ∉ insert (.channel 0) ({.base 40,.base 41} : Finset SourceName) :=
  scoped_output.fresh_prenex _

abbrev oldContext : Named (Fin 1) := .embed (.active 0 (.unary .pk (.name 42)))

/-- The same untouched old key context shifts at the target of parallel output. -/
theorem parallel_bound_retains_shifted_context :
    ∃ (ns : List SourceName) (a : Extended (Fin 1)) (b : Extended (Option (Fin 1))),
      Named.Structural (.par source oldContext) (Named.restrictNames ns (.embed a)) ∧
      Named.Structural (.par target (oldContext.rename some)) (Named.restrictNames ns (.embed b)) ∧
      Extended.BoundOutput a 0 b ∧ ∀ n ∈ ns, n ≠ SourceName.channel 0 :=
  (Named.BoundOutput.parLeft oldContext scoped_output).prenex

theorem old_context_is_not_fresh_export :
    (oldContext.rename some).freeNames = oldContext.freeNames ∧
    oldContext.rename some = .embed (.active (some (0 : Fin 1)) (.unary .pk (.name 42))) ∧
    oldContext.rename some ≠ .embed (.active none (.unary .pk (.name 42))) := by
  exact ⟨Named.freeNames_rename _ _,rfl,by intro h; cases h⟩

/-- Scope's old local and exported variable remain exchanged under another
injective outer renaming; neither is confused with old Some(Some v). -/
theorem scoped_exchange_survives_outer_renaming :
    ((Named.embed (.active (some none : Option (Option Nat)) (.var none))).rename Extended.swapBinders).rename
      (Option.map (Option.map some)) =
    ((Named.embed (.active (some none : Option (Option Nat)) (.var none))).rename
      (Option.map (Option.map some))).rename Extended.swapBinders :=
  Named.rename_swapBinders _ some

theorem private_bound_output_still_blocked (b : Named (Option (Fin 1))) :
    ¬ Named.BoundOutput (.newName (.channel 0) source) 0 b := by
  intro h
  have hm := h.channel_mem
  exact (by simp [Named.channels] : 0 ∉ (Named.newName (.channel 0) source).channels) hm

/-- An actual complete frame capture also factors under its enclosing private
key name, with the original public channel and full raw target. -/
theorem actual_frame_capture_factors :
    ∃ (ns : List SourceName) (a : Extended (Fin 1)) (b : Extended (Option (Fin 1))),
      Named.Structural
        (.newName (.base 40) (.embed (frameProcess SourceAtomicOutputSPOT.oldFrame
          (.output 0 SourceVisibleInterpretationSPOT.proofPayload .nil))))
        (Named.restrictNames ns (.embed a)) ∧
      Named.Structural
        (.newName (.base 40) (.embed (.par ((activeFrame SourceAtomicOutputSPOT.oldFrame).rename some)
          (capture (groundTerm SourceVisibleInterpretationSPOT.proofPayload) (groundAgent Agent.nil)))))
        (Named.restrictNames ns (.embed b)) ∧ Extended.BoundOutput a 0 b ∧
      ∀ n ∈ ns, n ≠ SourceName.channel 0 :=
  (Named.BoundOutput.scopeName (.base 40) (by decide) (.embed (frame_output_derivable _ _ _ _))).prenex

end ExplainableCrypto.Helios.Symbolic.SourceBoundPrenexSPOT
