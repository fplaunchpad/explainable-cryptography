import ExplainableCrypto.Helios.Computational.BitOraclePrimitiveLoop

/-! Every existing tape-loop action has an actual finite primitive execution.
The local bound exposes which fixed-program support remains to be discharged
when composing arbitrary reachable runs and common clocks. -/
namespace ExplainableCrypto.Helios.Computational.BitOraclePrimitiveLoop
open Turing OracleComp OracleSpec BitOraclePortTransfer

/-- This local allowance will be bounded by the global fixed-code multiplier
on the successor-closed support. Pure terminal call dispatch costs zero. -/
def stepAllowance {s l m : Nat} (code : BitOracleMachine.Code s l m) :
    BitOracleTapeLoop.State s l m → Nat
  | .compute source cfg _ _ => match cfg.l with
    | none => 1
    | some label => TM1PrimitiveCost.allowance
        (TM2to1.tr (BitOracleTapeLoop.localProgram code source) label)
  | .prepare request _ cfg _ _ => match cfg.l with
    | none => 1
    | some label => TM1PrimitiveCost.allowance (TM2to1.tr (requestProgram request) label)
  | .call _ (.response destination cfg _ _) => match cfg.l with
    | none => 1
    | some label => TM1PrimitiveCost.allowance (TM2to1.tr (program destination) label)
  | .call _ (.done _ _ _) => 0
  | _ => 1

private theorem phase_segment {s l m : Nat} {A : Type} (code : BitOracleMachine.Code s l m)
    (f : A → A) (finished : A → Prop) [DecidablePred finished] (embed : A → State s l m)
    (hs : ∀ a, ¬ finished a → step code (embed a) = pure (embed (f a)))
    (hf : ∀ a, finished a → f a = a) (fuel : Nat) (a : A) :
    ∃ used ≤ fuel, run code used (embed a) = pure (embed (f^[fuel] a)) := by
  induction fuel generalizing a with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ fuel ih =>
    by_cases h : finished a
    · exact ⟨0, Nat.zero_le _, by rw [Function.iterate_fixed (hf a h)]; rfl⟩
    · obtain ⟨used, hu, he⟩ := ih (f a)
      refine ⟨used + 1, by omega, ?_⟩
      rw [run, hs a h, pure_bind, he, Function.iterate_succ_apply]

private theorem statement_segment {s l m : Nat} {Γ L V : Type} [Inhabited Γ]
    (code : BitOracleMachine.Code s l m) (M : L → TM1.Stmt Γ L V)
    (embed : TM0.Cfg Γ (TM1to0.Λ' M) → State s l m)
    (hs : ∀ c, c.q.1.isNone = false → step code (embed c) = pure (embed (primitiveTick M c)))
    (label : L) (memory : V) (tape : Tape Γ) :
    ∃ used ≤ TM1PrimitiveCost.allowance (M label),
      run code used (embed (TM1to0.trCfg M ⟨some label, memory, tape⟩)) =
        pure (embed (TM1to0.trCfg M (TM1.stepAux (M label) memory tape))) := by
  let _ : Inhabited L := ⟨label⟩
  let _ : Inhabited V := ⟨memory⟩
  obtain ⟨used, hu, he⟩ := phase_segment code (primitiveTick M) (fun c => c.q.1.isNone = true) embed
    (fun c h => hs c (Bool.eq_false_iff.mpr h))
    (by intro c h; cases c with
        | mk control tape => cases control with
          | mk q v => cases q <;> simp_all [primitiveTick])
    (TM1PrimitiveCost.work (M label) memory tape)
    (TM1to0.trCfg M ⟨some label, memory, tape⟩)
  have ht : primitiveTick M = TM1PrimitiveCost.tick M := funext (primitiveTick_eq M)
  rw [ht] at he
  exact ⟨used, hu.trans (TM1PrimitiveCost.work_le _ _ _),
    he.trans (congrArg (fun c => pure (embed c))
      (TM1PrimitiveCost.statement M (M label) memory tape))⟩

/-- Every old-loop action is realized by actual primitive execution, including
all native answers. No presentation or correspondence certificate is supplied. -/
theorem step_match {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (cfg : BitOracleTapeLoop.State s l m) :
    ∃ used ≤ stepAllowance code cfg,
      run code used (lower code cfg) = lower code <$> BitOracleTapeLoop.step code cfg := by
  cases cfg with
  | ready label memory tapes =>
    refine ⟨1, le_rfl, ?_⟩
    cases label with
    | none => rfl
    | some source => cases h : code source <;>
        simp [run, lower, step, BitOracleTapeLoop.step, h, TM1to0.trCfg] <;> rfl
  | compute source cfg query answer =>
    cases cfg with
    | mk label memory tape => cases label with
      | none => exact ⟨1, le_rfl, rfl⟩
      | some label =>
        obtain ⟨used, hu, he⟩ := statement_segment code
          (TM2to1.tr (BitOracleTapeLoop.localProgram code source))
          (fun c => State.compute source c query answer)
          (by intro c h; simp only [step, h, Bool.false_eq_true, ↓reduceIte]) label memory tape
        exact ⟨used, hu, he⟩
  | prepare request destination cfg query answer =>
    cases cfg with
    | mk label memory tape => cases label with
      | none => exact ⟨1, le_rfl, rfl⟩
      | some label =>
        obtain ⟨used, hu, he⟩ := statement_segment code (TM2to1.tr (requestProgram request))
          (fun c => State.prepare request destination c query answer)
          (by intro c h; simp only [step, h, Bool.false_eq_true, ↓reduceIte]) label memory tape
        exact ⟨used, hu, he⟩
  | call kind cfg => cases cfg with
    | output destination saved cfg answer =>
      refine ⟨1, le_rfl, ?_⟩
      by_cases h : cfg.phase = .done <;>
        simp [run, lower, step, BitOracleTapeLoop.step, BitOracleTapeCall.step, h]
    | issue destination saved tapes =>
      refine ⟨1, le_rfl, ?_⟩
      simp only [run, lower, step, BitOracleTapeLoop.step, BitOracleTapeCall.step,
        bind_pure, map_bind, map_pure]
    | input destination saved query cfg =>
      refine ⟨1, le_rfl, ?_⟩
      by_cases h : cfg.phase = .done
      · simp [run, lower, step, BitOracleTapeLoop.step, BitOracleTapeCall.step, h, TM1to0.trCfg]
        rfl
      · simp [run, lower, step, BitOracleTapeLoop.step, BitOracleTapeCall.step, h]
    | response destination cfg query answer =>
      cases cfg with
      | mk label memory tape => cases label with
        | none => exact ⟨1, le_rfl, rfl⟩
        | some label =>
          obtain ⟨used, hu, he⟩ := statement_segment code (TM2to1.tr (program destination))
            (fun c => State.response destination c query answer)
            (by intro c h; simp only [step, h, Bool.false_eq_true, ↓reduceIte]) label memory tape
          exact ⟨used, hu, he⟩
    | done cfg query answer => exact ⟨0, le_rfl, rfl⟩

end ExplainableCrypto.Helios.Computational.BitOraclePrimitiveLoop
