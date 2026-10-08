import ExplainableCrypto.Helios.Computational.BitOraclePrimitiveCorrespondence
import ExplainableCrypto.Helios.Computational.BitOracleTapeBounded

/-! Common primitive clocks derived from the existing source halt/charge
contract and actual tape-loop correspondence. No compiler certificate is added. -/
namespace ExplainableCrypto.Helios.Computational.BitOraclePrimitiveBounded
open Turing OracleComp OracleSpec BitOraclePrimitiveLoop
open OracleTapeOutput (wordTape)
open BitOracleLoopBounded (Allowed Within adapter)

/-- A terminal old-loop boundary, used only to justify common-clock padding. -/
def Halted {s l m : Nat} : BitOracleTapeLoop.State s l m → Prop
  | .ready none _ _ => True
  | _ => False

private theorem run_halted {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (fuel : Nat) (cfg : BitOracleTapeLoop.State s l m) (h : Halted cfg) :
    run code fuel (lower code cfg) = pure (lower code cfg) := by
  cases cfg with
  | ready label memory tapes => cases label with
    | none => induction fuel with
      | zero => rfl
      | succ fuel ih => simpa only [run, lower, step, pure_bind] using ih
    | some => contradiction
  | compute | prepare | call => contradiction

private theorem adapter_node {A : Type} (limit : Nat) (q : BitOracleMachine.Request)
    (next : BitOracleMachine.spec.Range q → OracleComp BitOracleMachine.spec A) :
    simulateQ (adapter limit) (OracleComp.queryBind q next) =
      (liftM ((BitOracleLoopBounded.spec limit).query q) >>= fun answer =>
        simulateQ (adapter limit) (next answer.val)) := rfl

private theorem child_mem {A : Type} (limit : Nat) (q : BitOracleMachine.Request)
    (next : BitOracleMachine.spec.Range q → OracleComp BitOracleMachine.spec A)
    (answer : (BitOracleLoopBounded.spec limit).Range q) (out : A)
    (h : out ∈ support (simulateQ (adapter limit) (next answer.val))) :
    out ∈ support (simulateQ (adapter limit) (OracleComp.queryBind q next)) := by
  rw [adapter_node, support_bind]
  exact Set.mem_iUnion.mpr ⟨answer, Set.mem_iUnion.mpr ⟨by simp [OracleComp.support_liftM], h⟩⟩

private theorem within_halts {s l m : Nat}
    (oa : OracleComp BitOracleMachine.spec (BitOracleMachine.Config s l m × Nat))
    (limit bound : Nat) (h : Within limit bound oa) :
    ∀ out ∈ support (simulateQ (adapter limit) oa), out.1.l = none := by
  induction oa with
  | pure out => simpa [simulateQ_pure] using h.1
  | queryBind q next ih =>
    intro out ho
    rw [adapter_node] at ho
    obtain ⟨answer, _, hr⟩ := OracleComp.mem_support_bind_peel _ _ ho
    exact ih answer.val (h answer.val answer.property) out hr

/-- Interpret the full caller only at a ready boundary. This is proof-side
observation, not an executed decoder or an added protocol disclosure. -/
def observe {s l m : Nat} : State s l m → Option (BitOracleMachine.Config s l m)
  | .ready label memory tapes => BitOracleTapeLoop.observeCaller (.ready label memory tapes)
  | _ => none

private theorem halted_of_observe {s l m : Nat} (state : BitOracleTapeLoop.State s l m)
    (cfg : BitOracleMachine.Config s l m) (he : BitOracleTapeLoop.observeCaller state = some cfg)
    (hh : cfg.l = none) : Halted state := by
  cases state with
  | ready label memory tapes =>
    have hcfg := Option.some.inj he
    have hl := congrArg (fun c : BitOracleMachine.Config s l m => c.l) hcfg
    simp only at hl
    have hn : label = none := hl.trans hh
    simp [Halted, hn]
  | compute | prepare | call => cases he

private theorem observe_lower_halted {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (cfg : BitOracleTapeLoop.State s l m) (h : Halted cfg) :
    observe (lower code cfg) = BitOracleTapeLoop.observeCaller cfg := by
  cases cfg with
  | ready => rfl
  | compute | prepare | call => contradiction

/-- A compiled tree whose permitted leaves halt can be observed at one clock.
Exact full lowered states and all native query branches are preserved. -/
theorem compiled_run {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (oa : OracleComp BitOracleMachine.spec (BitOracleTapeLoop.State s l m))
    (limit bound : Nat) (cfg : State s l m) (h : Compiled code oa bound cfg)
    (hh : ∀ out ∈ support (simulateQ (adapter limit) oa), Halted out) :
    simulateQ (adapter limit) (run code bound cfg) = lower code <$> simulateQ (adapter limit) oa := by
  induction oa generalizing bound cfg with
  | pure out =>
    obtain ⟨used, hu, he⟩ := h
    have ho : Halted out := hh out (by simp)
    have hn : bound = used + (bound - used) := by omega
    rw [hn, run_add, he, pure_bind, run_halted code _ _ ho]
    simp only [simulateQ_pure]
    rfl
  | queryBind q next ih =>
    obtain ⟨before, hb, continuation, he, hn⟩ := h
    have ht : bound = before + (bound - before) := by omega
    rw [ht, run_add, he]
    change simulateQ (adapter limit)
      (liftM (BitOracleMachine.spec.query q) >>= fun answer => run code (bound - before) (continuation answer)) = _
    rw [show (liftM (BitOracleMachine.spec.query q) >>= fun answer => run code (bound - before) (continuation answer)) =
      OracleComp.queryBind q (fun answer => run code (bound - before) (continuation answer)) from rfl]
    rw [adapter_node, adapter_node, map_bind]
    apply bind_congr
    intro answer
    exact ih answer.val _ _ (hn answer.val)
      (fun out ho => hh out (child_mem limit q next answer out ho))

private theorem tape_halts {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (sourceFuel limit bound : Nat) (cfg : BitOracleMachine.Config s l m)
    (previous : List Bool) (oldAnswer : Tape (Option Bool))
    (h : Within limit bound (BitOracleMachine.run code sourceFuel cfg)) :
    let cap := TM2TapeRuns.height cfg.stk + bound + previous.length
    ∀ out ∈ support (simulateQ (adapter limit)
      (BitOracleTapeLoop.run code (BitOracleTapeCap.unitCost cap * bound)
        (BitOracleTapeLoop.ready cfg (wordTape previous) oldAnswer))), Halted out := by
  dsimp only
  intro out ho
  have he := BitOracleTapeLoop.run_source_bounded code sourceFuel limit bound cfg previous oldAnswer h
  have hv : BitOracleTapeLoop.observeCaller out ∈ support
      (BitOracleTapeLoop.observeCaller <$> simulateQ (adapter limit)
        (BitOracleTapeLoop.run code (BitOracleTapeCap.unitCost
          (TM2TapeRuns.height cfg.stk + bound + previous.length) * bound)
          (BitOracleTapeLoop.ready cfg (wordTape previous) oldAnswer))) := by
    rw [support_map]
    exact ⟨out, ho, rfl⟩
  rw [he, support_map] at hv
  obtain ⟨sourceOut, hs, heq⟩ := hv
  exact halted_of_observe out sourceOut.1 heq.symm
    (within_halts _ limit bound h sourceOut hs)

/-- The existing source charge/termination contract derives the complete
primitive common-clock correspondence. The clock is G times the tape clock. -/
theorem run_source_bounded {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (sourceFuel limit bound : Nat) (cfg : BitOracleMachine.Config s l m)
    (previous : List Bool) (oldAnswer : Tape (Option Bool))
    (h : Within limit bound (BitOracleMachine.run code sourceFuel cfg)) :
    let cap := TM2TapeRuns.height cfg.stk + bound + previous.length
    let clock := BitOracleTapeCap.unitCost cap * bound
    observe <$> simulateQ (adapter limit)
      (run code (clock * globalFactor code)
        (lower code (BitOracleTapeLoop.ready cfg (wordTape previous) oldAnswer))) =
      (fun out => some out.1) <$> simulateQ (adapter limit) (BitOracleMachine.run code sourceFuel cfg) := by
  dsimp only
  have hh := tape_halts code sourceFuel limit bound cfg previous oldAnswer h
  have hc := run_ready code (BitOracleTapeCap.unitCost
    (TM2TapeRuns.height cfg.stk + bound + previous.length) * bound) cfg (wordTape previous) oldAnswer
  rw [compiled_run code _ limit _ _ hc hh]
  have hv : (fun out => observe (lower code out)) <$>
      simulateQ (adapter limit) (BitOracleTapeLoop.run code (BitOracleTapeCap.unitCost
        (TM2TapeRuns.height cfg.stk + bound + previous.length) * bound)
          (BitOracleTapeLoop.ready cfg (wordTape previous) oldAnswer)) =
      BitOracleTapeLoop.observeCaller <$> simulateQ (adapter limit)
        (BitOracleTapeLoop.run code (BitOracleTapeCap.unitCost
          (TM2TapeRuns.height cfg.stk + bound + previous.length) * bound)
            (BitOracleTapeLoop.ready cfg (wordTape previous) oldAnswer)) := by
    simp only [map_eq_bind_pure_comp, Function.comp_def]
    apply OracleComp.bind_congr_of_forall_mem_support
    intro out ho
    rw [observe_lower_halted code out (hh out ho)]
  simpa only [Functor.map_map, Function.comp_def] using
    hv.trans (BitOracleTapeLoop.run_source_bounded code sourceFuel limit bound cfg previous oldAnswer h)

/-- Every lawful bounded-oracle handler preserves its complete effects at the
derived primitive source clock, including probabilistic stateful handlers. -/
theorem run_source_handler {s l m : Nat} {M : Type → Type} [Monad M] [LawfulMonad M]
    (code : BitOracleMachine.Code s l m) (sourceFuel limit bound : Nat)
    (cfg : BitOracleMachine.Config s l m) (previous : List Bool) (oldAnswer : Tape (Option Bool))
    (h : Within limit bound (BitOracleMachine.run code sourceFuel cfg))
    (handler : QueryImpl (BitOracleLoopBounded.spec limit) M) :
    let cap := TM2TapeRuns.height cfg.stk + bound + previous.length
    let clock := BitOracleTapeCap.unitCost cap * bound
    observe <$> simulateQ handler (simulateQ (adapter limit)
      (run code (clock * globalFactor code)
        (lower code (BitOracleTapeLoop.ready cfg (wordTape previous) oldAnswer)))) =
      (fun out => some out.1) <$>
        simulateQ handler (simulateQ (adapter limit) (BitOracleMachine.run code sourceFuel cfg)) := by
  simpa only [simulateQ_map] using congrArg (simulateQ handler)
    (run_source_bounded code sourceFuel limit bound cfg previous oldAnswer h)

end ExplainableCrypto.Helios.Computational.BitOraclePrimitiveBounded
