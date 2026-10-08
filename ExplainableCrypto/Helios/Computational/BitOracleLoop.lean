import ExplainableCrypto.Helios.Computational.BitOraclePortTransfer

/-! A fixed finite-control execution loop for the raw oracle stack machine.
All unbounded data are bit stacks. A step inspects only finite control, executes
one existing TM2 statement, or performs one native query. Observation fuel is
external to the machine; no word length determines its transition function. -/
namespace ExplainableCrypto.Helios.Computational.BitOracleLoop
open OracleComp OracleSpec Turing.TM2
open BitOraclePortTransfer

inductive State (s l m : Nat) where
  | ready (cfg : BitOracleMachine.Config s l m)
  | request (source destination : Fin s) (cfg : Config s l m)
  | response (destination : Fin s) (cfg : Config s l m)

/-- Ready states have empty private workspace. Dispatch only selects finite
control and exposes the same caller stacks through the established layout. -/
def step {s l m : Nat} (code : BitOracleMachine.Code s l m) :
    State s l m → OracleComp BitOracleMachine.spec (State s l m)
  | .ready cfg => match cfg.l with
    | none => pure (.ready cfg)
    | some label => match code label with
      | .compute stmt => pure (.ready (stepAux stmt cfg.var cfg.stk))
      | .hash source destination next =>
          pure (.request source destination (requestStart cfg source next []))
      | .coin destination next =>
          State.response destination <$> nativeCoin
            {requestStart cfg destination next [] with l := none}
  | .request source destination cfg => match cfg.l with
    | some _ => pure (.request source destination
        (TM2ReturnLink.tick (requestProgram source) cfg))
    | none => State.response destination <$> nativeHash cfg
  | .response destination cfg => match cfg.l with
    | some _ => pure (.response destination (TM2ReturnLink.tick (program destination) cfg))
    | none => pure (.ready (project cfg))

/-- Micro-step fuel limits observation, including native events and dispatch. -/
def run {s l m : Nat} (code : BitOracleMachine.Code s l m) :
    Nat → State s l m → OracleComp BitOracleMachine.spec (State s l m)
  | 0, cfg => pure cfg
  | n + 1, cfg => do
      let next ← step code cfg
      run code n next

/-- Split observations at any intermediate machine state. -/
theorem run_add {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (a b : Nat) (cfg : State s l m) :
    run code (a + b) cfg = (run code a cfg >>= run code b) := by
  induction a generalizing cfg with
  | zero => simp [run]
  | succ a ih => simp [Nat.succ_add, run, ih, bind_assoc]

/-- A halted padded TM2 phase can be stopped at its first completion inside
this loop. Only active phase steps are taken, so no native event is consumed. -/
private theorem phase_run {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (p : BitPortTransfer.Label → Stmt (fun _ : Ports s => Bool)
      BitPortTransfer.Label ((Fin l × Fin m) × Option Bool))
    (wrap : Config s l m → State s l m)
    (hs : ∀ cfg, cfg.l ≠ none →
      step code (wrap cfg) = pure (wrap (TM2ReturnLink.tick p cfg)))
    (fuel : Nat) (cfg : Config s l m)
    (halted : ((TM2ReturnLink.tick p)^[fuel] cfg).l = none) :
    ∃ used ≤ fuel, run code used (wrap cfg) =
      pure (wrap ((TM2ReturnLink.tick p)^[fuel] cfg)) := by
  induction fuel generalizing cfg with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ fuel ih =>
    by_cases h : cfg.l = none
    · have fixed : TM2ReturnLink.tick p cfg = cfg := by
        cases cfg with
        | mk label v tapes => cases label <;> simp_all [TM2ReturnLink.tick, Turing.TM2.step]
      exact ⟨0, Nat.zero_le _, by rw [Function.iterate_fixed fixed]; rfl⟩
    · rw [Function.iterate_succ_apply] at halted
      obtain ⟨used, hu, he⟩ := ih _ halted
      refine ⟨used + 1, by omega, ?_⟩
      rw [run, hs cfg h, pure_bind, he, Function.iterate_succ_apply]

/-- Prepare a physical request without issuing it, preserving every caller
stack and the full saved continuation. No first-halt premise is required. -/
theorem request_run {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (cfg : BitOracleMachine.Config s l m) (source destination : Fin s) (next : Fin l) :
    ∃ used ≤ 2 * (cfg.stk source).length + 4,
      run code used (.request source destination (requestStart cfg source next [])) =
        pure (.request source destination
          {requestStart cfg source next (cfg.stk source) with l := none}) := by
  obtain ⟨fuel, hf, he⟩ := request_state cfg source next []
  obtain ⟨used, hu, hr⟩ := phase_run code (requestProgram source)
    (State.request source destination) (fun c h => by
      cases hl : c.l with
      | none => exact False.elim (h hl)
      | some label => simp [step, hl]) fuel (requestStart cfg source next [])
    (by rw [he])
  refine ⟨used, by simp only [List.length_nil, Nat.zero_add] at hf; omega, ?_⟩
  rwa [he] at hr

/-- Complete response loading and return to the caller. Empty private
workspace is derived before the projection discards the two private ports. -/
theorem response_run {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (cfg : BitOracleMachine.Config s l m) (destination : Fin s) (next : Fin l)
    (answer : List Bool) :
    ∃ used ≤ (cfg.stk destination).length + 3 * answer.length + 5,
      ∃ out : Config s l m,
        out.l = none ∧ out.stk (.inr false) = [] ∧ out.stk (.inr true) = [] ∧
        project out = BitOracleMachine.resume cfg destination next answer ∧
        run code used (.response destination (start cfg destination next answer)) =
          pure (.ready (BitOracleMachine.resume cfg destination next answer)) := by
  obtain ⟨fuel, hf, hh, hp, hi, ht⟩ := run_resume cfg destination next answer
  obtain ⟨used, hu, hr⟩ := phase_run code (program destination)
    (State.response destination) (fun c h => by
      cases hl : c.l with
      | none => exact False.elim (h hl)
      | some label => simp [step, hl]) fuel (start cfg destination next answer) hh
  refine ⟨used + 1, by omega, _, hh, hi, ht, hp, ?_⟩
  rw [run_add, hr, pure_bind]
  simp [run, step, hh, hp]

/-- Dispatch and preparation issue exactly the source hash query. All answers
start the checked response phase; no answer is inspected before the query. -/
theorem hash_issue {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (cfg : BitOracleMachine.Config s l m) (label : Fin l)
    (source destination : Fin s) (next : Fin l)
    (hl : cfg.l = some label) (hc : code label = .hash source destination next) :
    ∃ before ≤ 2 * (cfg.stk source).length + 6,
      run code before (.ready cfg) =
        (do let answer ← liftM (BitOracleMachine.spec.query (.hash (cfg.stk source)))
            pure (.response destination (start cfg destination next answer))) := by
  obtain ⟨used, hu, he⟩ := request_run code cfg source destination next
  refine ⟨(used + 1) + 1, by omega, ?_⟩
  have dispatch : step code (.ready cfg) =
      pure (.request source destination (requestStart cfg source next [])) := by
    simp only [step, hl, hc]
  rw [run, dispatch, pure_bind, run_add, he, pure_bind]
  simp only [run, step, bind_pure_comp]
  change State.response destination <$>
    nativeHash {requestStart cfg source next (cfg.stk source) with l := none} = _
  unfold nativeHash
  rw [(request_start cfg source source next (cfg.stk source)).2.1]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  apply bind_congr
  intro answer
  have hd := delivery_start cfg source destination next answer (cfg.stk source)
  exact congrArg (fun c => (pure (.response destination c) :
    OracleComp BitOracleMachine.spec (State s l m))) hd

/-- Each received answer returns to the exact successor boundary, with a bound
that includes dispatch, the native event and the response return. -/
theorem hash_cycle {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (cfg : BitOracleMachine.Config s l m) (label : Fin l)
    (source destination : Fin s) (next : Fin l)
    (hl : cfg.l = some label) (hc : code label = .hash source destination next) :
    ∃ before,
      run code before (.ready cfg) =
        (do let answer ← liftM (BitOracleMachine.spec.query (.hash (cfg.stk source)))
            pure (.response destination (start cfg destination next answer))) ∧
      ∀ answer : List Bool, ∃ after,
        before + after ≤ 11 * (1 + (cfg.stk source).length +
          (cfg.stk destination).length + answer.length) ∧
        run code after (.response destination (start cfg destination next answer)) =
          pure (.ready (BitOracleMachine.resume cfg destination next answer)) := by
  obtain ⟨before, hb, he⟩ := hash_issue code cfg label source destination next hl hc
  refine ⟨before, he, ?_⟩
  intro answer
  obtain ⟨after, ha, out, _, _, _, _, ho⟩ := response_run code cfg destination next answer
  exact ⟨after, by omega, ho⟩

/-- Coin dispatch uses the native bit query, then the same consuming loader. -/
theorem coin_cycle {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (cfg : BitOracleMachine.Config s l m) (label : Fin l)
    (destination : Fin s) (next : Fin l)
    (hl : cfg.l = some label) (hc : code label = .coin destination next) :
    step code (.ready cfg) =
      (do let bit ← liftM (BitOracleMachine.spec.query .coin)
          pure (.response destination (start cfg destination next [bit]))) ∧
    ∀ bit : Bool, ∃ after,
      1 + after ≤ 11 * (2 + (cfg.stk destination).length) ∧
      run code after (.response destination (start cfg destination next [bit])) =
        pure (.ready (BitOracleMachine.resume cfg destination next [bit])) := by
  constructor
  · simp only [step, hl, hc, coin_handoff, map_bind, map_pure]
  · intro bit
    obtain ⟨after, ha, out, _, _, _, _, ho⟩ := response_run code cfg destination next [bit]
    exact ⟨after, by simp only [List.length_cons, List.length_nil] at ha; omega, ho⟩

end ExplainableCrypto.Helios.Computational.BitOracleLoop
