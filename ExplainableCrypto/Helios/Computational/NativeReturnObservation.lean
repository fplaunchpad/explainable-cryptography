import ExplainableCrypto.Helios.Computational.NativeRoundTripMemory
import ExplainableCrypto.Helios.Computational.BitOracleReturnLink
import ExplainableCrypto.Helios.Computational.BitOracleStackFrame

/-! A bounded observation stops at a selected live native-entry boundary.
The controller and its labels remain unchanged; every non-stopped transition
is the actual BitOracleMachine.step. Candidate: stopped padding preserves the
returned live state, unlike ordinary execution padding. Literal controls below
retain that distinction. This is not a compiler or continuation-cost theorem. -/
namespace ExplainableCrypto.Helios.Computational.NativeReturnObservation
open Turing.TM2 OracleComp OracleSpec
variable {s l m : Nat}
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

def stopped (stop : Fin l → Bool) (cfg : BitOracleMachine.Config s l m) : Bool :=
  cfg.l.elim true stop

def run (stop : Fin l → Bool) (code : BitOracleMachine.Code s l m) :
    Nat → BitOracleMachine.Config s l m →
      OracleComp BitOracleMachine.spec (BitOracleMachine.Config s l m × Nat)
  | 0,cfg => pure (cfg,0)
  | fuel+1,cfg => if stopped stop cfg then pure (cfg,0) else do
      let first ← BitOracleMachine.step code cfg
      let last ← run stop code fuel first.1
      pure (last.1,first.2+last.2)

theorem run_succ_unstopped (stop : Fin l → Bool) (code : BitOracleMachine.Code s l m)
    (fuel : Nat) (cfg : BitOracleMachine.Config s l m) (hs : stopped stop cfg = false) :
    run stop code (fuel+1) cfg = (do
      let first ← BitOracleMachine.step code cfg
      let last ← run stop code fuel first.1
      pure (last.1,first.2+last.2)) := by simp [run,hs]

theorem stopped_run (stop : Fin l → Bool) (code : BitOracleMachine.Code s l m)
    (fuel : Nat) (cfg : BitOracleMachine.Config s l m) (hs : stopped stop cfg = true) :
    run stop code fuel cfg = pure (cfg,0) := by
  cases fuel <;> simp [run,hs]

theorem run_add (stop : Fin l → Bool) (code : BitOracleMachine.Code s l m)
    (a b : Nat) (cfg : BitOracleMachine.Config s l m) :
    run stop code (a+b) cfg = (do
      let first ← run stop code a cfg
      let last ← run stop code b first.1
      pure (last.1,first.2+last.2)) := by
  induction a generalizing cfg with
  | zero => simp [run]
  | succ a ih =>
    by_cases hs : stopped stop cfg = true
    · rw [stopped_run _ _ _ _ hs,stopped_run _ _ _ _ hs]
      simp [stopped_run _ _ _ _ hs]
    · simp [Nat.succ_add,run,hs,ih,bind_assoc,Nat.add_assoc]

/-- Extra observation fuel is safe only once the selected boundary is reached. -/
theorem stopped_padding (stop : Fin l → Bool) (code : BitOracleMachine.Code s l m)
    (fuel extra : Nat) (cfg last : BitOracleMachine.Config s l m) (charge : Nat)
    (hr : run stop code fuel cfg = pure (last,charge)) (hs : stopped stop last = true) :
    run stop code (fuel+extra) cfg = pure (last,charge) := by
  rw [run_add,hr]
  simp [stopped_run _ _ _ _ hs]

theorem padded (stop : Fin l → Bool) (code : BitOracleMachine.Code s l m)
    (fuel extra : Nat) (cfg : BitOracleMachine.Config s l m)
    (hs : ∀ out ∈ support (run stop code fuel cfg), stopped stop out.1 = true) :
    run stop code (fuel+extra) cfg = run stop code fuel cfg := by
  rw [run_add]
  conv_rhs => rw [← bind_pure (x := run stop code fuel cfg)]
  apply bind_congr_of_forall_mem_support
  intro out ho
  simp [stopped_run _ _ _ _ (hs out ho)]

/-- The same actual first-return prefix is visible to this observer. No source
label is a stop boundary; the return may be stopped or live for another phase. -/
theorem live_prefix {r : Nat}
    (p : Fin l → Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m))
    (q : BitOracleMachine.Code s r m) (labels : Fin l → Fin r) (ret : Fin r)
    (stop : Fin r → Bool) (hstop : ∀ label, stop (labels label) = false)
    (hq : ∀ label, q (labels label) = .compute (TM2ReturnLink.redirect labels ret (p label)))
    (bound : Nat) (hcost : ∀ label, BitOracleMachine.localCost (p label) ≤ bound)
    (fuel : Nat) (cfg : BitOracleMachine.Config s l m)
    (halted : ((TM2ReturnLink.tick p)^[fuel] cfg).l = none) :
    ∃ used ≤ fuel, ∃ charge ≤ bound*used,
      run stop q used (TM2ReturnLink.embed labels ret cfg) =
        pure (TM2ReturnLink.embed labels ret ((TM2ReturnLink.tick p)^[fuel] cfg),charge) := by
  induction fuel generalizing cfg with
  | zero => exact ⟨0,le_rfl,0,le_rfl,rfl⟩
  | succ fuel ih =>
    rcases cfg with ⟨label,v,words⟩
    cases label with
    | none =>
      have hi := Function.iterate_fixed
        (show TM2ReturnLink.tick p (⟨none,v,words⟩ : BitOracleMachine.Config s l m) =
          ⟨none,v,words⟩ from rfl) (fuel+1)
      refine ⟨0,Nat.zero_le _,0,le_rfl,?_⟩
      rw [hi]
      rfl
    | some label =>
      rw [Function.iterate_succ_apply] at halted
      obtain ⟨used,hu,charge,hcharge,hrun⟩ := ih _ halted
      have hs : BitOracleMachine.step q
          (TM2ReturnLink.embed labels ret (⟨some label,v,words⟩ : BitOracleMachine.Config s l m)) =
          pure (TM2ReturnLink.embed labels ret
            (TM2ReturnLink.tick p ⟨some label,v,words⟩),BitOracleMachine.localCost (p label)) := by
        simp only [BitOracleMachine.step,TM2ReturnLink.embed,Option.elim,hq,
          TM2ReturnLink.redirect_step,NativeRoundTripMemory.redirect_cost]
        rfl
      have hn : stopped stop (TM2ReturnLink.embed labels ret
          (⟨some label,v,words⟩ : BitOracleMachine.Config s l m)) = false := hstop label
      refine ⟨used+1,by omega,BitOracleMachine.localCost (p label)+charge,?_,?_⟩
      · have hc := hcost label
        rw [Nat.mul_add,Nat.mul_one]
        omega
      · rw [run_succ_unstopped _ _ _ _ hn,hs]
        simp only [pure_bind]
        rw [hrun]
        simp only [pure_bind,Function.iterate_succ_apply]

/-- Every observed endpoint, including its accumulated charge, occurs after
some bounded prefix of the unchanged controller. No stopped state is fabricated. -/
theorem actual_prefix (stop : Fin l → Bool) (code : BitOracleMachine.Code s l m)
    (fuel : Nat) (cfg : BitOracleMachine.Config s l m)
    (out : BitOracleMachine.Config s l m × Nat)
    (ho : out ∈ support (run stop code fuel cfg)) :
    ∃ used ≤ fuel, out ∈ support (BitOracleMachine.run code used cfg) := by
  induction fuel generalizing cfg out with
  | zero => exact ⟨0,le_rfl,ho⟩
  | succ fuel ih =>
    by_cases hs : stopped stop cfg = true
    · rw [stopped_run _ _ _ _ hs] at ho
      exact ⟨0,Nat.zero_le _,ho⟩
    · have hn : stopped stop cfg = false := by simpa using hs
      rw [run_succ_unstopped _ _ _ _ hn,mem_support_bind_iff] at ho
      obtain ⟨first,hfirst,hrest⟩ := ho
      rw [mem_support_bind_iff] at hrest
      obtain ⟨last,hlast,heq⟩ := hrest
      obtain ⟨used,hu,hactual⟩ := ih first.1 last hlast
      refine ⟨used+1,by omega,?_⟩
      rw [BitOracleMachine.run,mem_support_bind_iff]
      refine ⟨first,hfirst,?_⟩
      rw [mem_support_bind_iff]
      exact ⟨last,hactual,heq⟩

/-- Framing arbitrary private words preserves the entire observed query tree,
complete endpoint and exact accumulated charge. -/
theorem stackFrame_run {e t : Nat} (layout : Fin s ⊕ Fin e ≃ Fin t)
    (stop : Fin l → Bool) (code : BitOracleMachine.Code s l m)
    (fuel : Nat) (cfg : BitOracleMachine.Config s l m) (frame : Fin e → List Bool) :
    run stop (BitOracleStackFrame.code layout code) fuel (BitOracleStackFrame.embed layout cfg frame) =
      (fun out => (BitOracleStackFrame.embed layout out.1 frame,out.2)) <$>
        run stop code fuel cfg := by
  induction fuel generalizing cfg with
  | zero => simp [run]
  | succ fuel ih =>
    have he : stopped stop (BitOracleStackFrame.embed layout cfg frame) = stopped stop cfg := rfl
    by_cases hs : stopped stop cfg = true
    · rw [stopped_run _ _ _ _ (he.trans hs),stopped_run _ _ _ _ hs]
      rfl
    · have hn : stopped stop cfg = false := by simpa using hs
      rw [run_succ_unstopped _ _ _ _ (he.trans hn),BitOracleStackFrame.step,
        run_succ_unstopped _ _ _ _ hn]
      simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
      apply bind_congr
      intro first
      rw [ih]
      simp [map_eq_bind_pure_comp,bind_assoc]

private def liveControl : BitOracleMachine.Code 1 2 1 :=
  fun q => if q = 0 then .compute (.goto (fun _ => 1)) else .coin 0 1
private def controlStart : BitOracleMachine.Config 1 2 1 := ⟨some 0,0,fun _ => [true,false]⟩
private def controlStop (q : Fin 2) : Bool := q = 1

theorem stopped_live_control : run controlStop liveControl 10 controlStart =
    pure (⟨some 1,0,fun _ => [true,false]⟩,1) := by rfl

theorem ordinary_padding_queries :
    OracleComp.isPure (BitOracleMachine.run liveControl 2 controlStart) = false := by rfl

theorem prematurely_stopped_control : run (fun _ => true) liveControl 10 controlStart =
    pure (controlStart,0) := by rfl

end ExplainableCrypto.Helios.Computational.NativeReturnObservation
