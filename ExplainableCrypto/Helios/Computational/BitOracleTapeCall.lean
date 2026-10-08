import ExplainableCrypto.Helios.Computational.OracleTapeDispatch
import ExplainableCrypto.Helios.Computational.BitOracleTapeInput
import ExplainableCrypto.Helios.Computational.BitOracleTapeOutput

/-! One native call loop: head-local export, an actual oracle event, physical
answer loading and the existing TM1 response program. Fuel is external. -/
namespace ExplainableCrypto.Helios.Computational.BitOracleTapeCall
open Turing OracleComp OracleSpec TM2TapeRuns BitOraclePortTransfer OracleTapeOutput

abbrev ResponseConfig (s l m : Nat) := TM2TapeCost.Config (K := Ports s)
  (Γ := fun _ => Bool) (Λ := BitPortTransfer.Label) (V := (Fin l × Fin m) × Option Bool)

inductive State (s l m : Nat) where
  | output (destination : Fin s) (saved : Fin l × Fin m)
      (cfg : OracleTapeOutput.Config (Ports s)) (oldAnswer : Tape (Option Bool))
  | issue (destination : Fin s) (saved : Fin l × Fin m) (tapes : OracleTapeDispatch.Tapes (Ports s))
  | input (destination : Fin s) (saved : Fin l × Fin m)
      (query : Tape (Option Bool)) (cfg : OracleTapeInput.Config (Ports s))
  | response (destination : Fin s) (cfg : ResponseConfig s l m)
      (query answer : Tape (Option Bool))
  | done (cfg : ResponseConfig s l m) (query answer : Tape (Option Bool))

/-- Phase changes copy only finite control; the existing work/native tapes
remain explicit. Only `issue` invokes the native oracle. -/
def step {s l m : Nat} (kind : OracleTapeDispatch.Kind) : State s l m →
    OracleComp BitOracleMachine.spec (State s l m)
  | .output destination saved cfg oldAnswer =>
      if cfg.phase = .done then pure (.issue destination saved ⟨cfg.work, cfg.query, oldAnswer⟩)
      else pure (.output destination saved (OracleTapeOutput.step (.inr false) cfg) oldAnswer)
  | .issue destination saved tapes => do
      let reply ← OracleTapeDispatch.dispatch kind tapes
      pure (.input destination saved reply.query ⟨.seekWork, reply.work, reply.answer⟩)
  | .input destination saved query cfg =>
      if cfg.phase = .done then pure (.response destination
        ⟨some (.normal .clear), (saved, none), cfg.work⟩ query cfg.answer)
      else pure (.input destination saved query (OracleTapeInput.step (.inr false) cfg))
  | .response destination cfg query answer =>
      if cfg.l.isNone then pure (.done cfg query answer)
      else pure (.response destination (TM2TapeCost.tick (program destination) cfg) query answer)
  | .done cfg query answer => pure (.done cfg query answer)

/-- Count actual call-loop transitions, including phase dispatch and native events. -/
def run {s l m : Nat} (kind : OracleTapeDispatch.Kind) : Nat → State s l m →
    OracleComp BitOracleMachine.spec (State s l m)
  | 0, cfg => pure cfg
  | n + 1, cfg => do
      let next ← step kind cfg
      run kind n next

theorem run_add {s l m : Nat} (kind : OracleTapeDispatch.Kind) (a b : Nat) (cfg : State s l m) :
    run kind (a + b) cfg = (run kind a cfg >>= run kind b) := by
  induction a generalizing cfg with
  | zero => simp [run]
  | succ a ih => simp [Nat.succ_add, run, ih, bind_assoc]

/-- Stop a pure region at first completion, before the surrounding loop can
issue a native query or enter a different region. Used for all three regions. -/
private theorem phase_run {s l m : Nat} {A : Type} (kind : OracleTapeDispatch.Kind)
    (f : A → A) (finished : A → Prop) [DecidablePred finished]
    (embed : A → State s l m)
    (hs : ∀ a, ¬ finished a → step kind (embed a) = pure (embed (f a)))
    (hf : ∀ a, finished a → f a = a)
    (fuel : Nat) (a : A) (ha : finished (f^[fuel] a)) :
    ∃ used ≤ fuel, run kind used (embed a) = pure (embed (f^[fuel] a)) := by
  induction fuel generalizing a with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ fuel ih =>
    by_cases h : finished a
    · exact ⟨0, Nat.zero_le _, by rw [Function.iterate_fixed (hf a h)]; rfl⟩
    · rw [Function.iterate_succ_apply] at ha
      obtain ⟨used, hu, he⟩ := ih _ ha
      refine ⟨used + 1, by omega, ?_⟩
      rw [run, hs a h, pure_bind, he, Function.iterate_succ_apply]

/-- The actual completed request configuration, with its saved finite context. -/
def prepared {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (request : Fin s) (next : Fin l) (word : List Bool) : BitOraclePortTransfer.Config s l m :=
  {requestStart cfg request next word with l := none}

/-- Entry after actual request preparation; previous native tapes are explicit. -/
def begin {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (request destination : Fin s) (next : Fin l) (previous : List Bool)
    (oldAnswer : Tape (Option Bool)) : State s l m :=
  .output destination (next, cfg.var)
    ⟨.clear, (pack (prepared cfg request next (cfg.stk request))).Tape, wordTape previous⟩ oldAnswer

/-- A native word begins physical loading with the existing work/query tapes. -/
def received {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (request destination : Fin s) (next : Fin l) (oldPort : List Bool)
    (query : Tape (Option Bool)) (answer : List Bool) : State s l m :=
  .input destination (next, cfg.var) query
    ⟨.seekWork, (pack (prepared cfg request next oldPort)).Tape, wordTape answer⟩

/-- Hash replies retain the query just issued and its private request word. -/
def incoming {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (request destination : Fin s) (next : Fin l) (answer : List Bool) : State s l m :=
  received cfg request destination next (cfg.stk request) (wordTape (cfg.stk request)) answer

/-- Pure export reaches the native issue boundary before any answer is chosen. -/
theorem export_run {s l m : Nat} (kind : OracleTapeDispatch.Kind)
    (cfg : BitOracleMachine.Config s l m) (request destination : Fin s) (next : Fin l)
    (previous : List Bool) (oldAnswer : Tape (Option Bool)) :
    ∃ used ≤ previous.length + 2 * (cfg.stk request).length + 4,
      run kind used (begin cfg request destination next previous oldAnswer) =
        pure (.issue destination (next, cfg.var)
          ⟨(pack (prepared cfg request next (cfg.stk request))).Tape,
            wordTape (cfg.stk request), oldAnswer⟩) := by
  have hr := OracleTapeOutput.run_replacing
    (prepared cfg request next (cfg.stk request)) (.inr false) previous
  have hp : (prepared cfg request next (cfg.stk request)).stk (.inr false) = cfg.stk request :=
    (request_start cfg request request next (cfg.stk request)).2.1
  rw [hp] at hr
  obtain ⟨used, hu, he⟩ := phase_run kind (OracleTapeOutput.step (.inr false : Ports s))
    (fun c => c.phase = .done) (fun c => State.output destination (next, cfg.var) c oldAnswer)
    (by intro c h; simp only [step, h, ↓reduceIte])
    (by intro c h; simp only [OracleTapeOutput.step, h])
    _ _ (by rw [hr])
  rw [hr] at he
  refine ⟨used + 1, by omega, ?_⟩
  rw [begin, run_add, he, pure_bind]
  rfl

/-- Actual export, finite dispatch and the native event issue exactly the source
hash word. No answer is read before that event. -/
theorem hash_issue {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (request destination : Fin s) (next : Fin l) (previous : List Bool)
    (oldAnswer : Tape (Option Bool)) :
    ∃ before ≤ previous.length + 2 * (cfg.stk request).length + 5,
      run .hash before (begin cfg request destination next previous oldAnswer) =
        (do let answer ← liftM (BitOracleMachine.spec.query (.hash (cfg.stk request)))
            pure (incoming cfg request destination next answer)) := by
  obtain ⟨used, hu, he⟩ := export_run .hash cfg request destination next previous oldAnswer
  refine ⟨used + 1, by omega, ?_⟩
  rw [run_add, he, pure_bind]
  simp only [run, step]
  rw [OracleTapeDispatch.hash_word]
  simp only [bind_assoc, pure_bind]
  rfl

private theorem input_run {s l m : Nat} (kind : OracleTapeDispatch.Kind)
    (cfg : BitOracleMachine.Config s l m) (request destination : Fin s) (next : Fin l)
    (oldPort : List Bool) (query : Tape (Option Bool)) (answer : List Bool) :
    ∃ used ≤ 3 * oldPort.length + 4 * answer.length + 7,
      run kind used (received cfg request destination next oldPort query answer) =
        pure (.response destination (pack (start cfg destination next answer))
          query (wordTape answer)) := by
  have hr := BitOracleTapeInput.load_request cfg request destination next oldPort answer
  obtain ⟨used, hu, he⟩ := phase_run kind (OracleTapeInput.step (.inr false : Ports s))
    (fun c => c.phase = .done)
    (fun c => State.input destination (next, cfg.var) query c)
    (by intro c h; simp only [step, h, ↓reduceIte])
    (by intro c h; simp only [OracleTapeInput.step, h])
    _ _ (by rw [hr])
  rw [hr] at he
  refine ⟨used + 1, by omega, ?_⟩
  rw [received, prepared, run_add, he, pure_bind]
  rfl

private theorem response_run {s l m : Nat} (kind : OracleTapeDispatch.Kind)
    (cfg : BitOracleMachine.Config s l m) (destination : Fin s) (next : Fin l)
    (answer : List Bool) (query : Tape (Option Bool)) :
    let B := (cfg.stk destination).length + 3 * answer.length + 4
    ∃ used ≤ B * (6 * height (start cfg destination next answer).stk + 18 * B + 7) + 1,
      ∃ out : BitOraclePortTransfer.Config s l m,
        out.l = none ∧ project out = BitOracleMachine.resume cfg destination next answer ∧
        out.stk (.inr false) = [] ∧ out.stk (.inr true) = [] ∧
        run kind used (.response destination (pack (start cfg destination next answer)) query (wordTape answer)) =
          pure (.done (pack out) query (wordTape answer)) := by
  dsimp only
  obtain ⟨fuel, hf, out, ht, hh, hp, hi, hs⟩ := BitOracleTapeCost.response_run cfg destination next answer
  obtain ⟨used, hu, he⟩ := phase_run kind (TM2TapeCost.tick (program destination))
    (fun c => c.l.isNone = true) (fun c => State.response destination c query (wordTape answer))
    (by
      intro c h
      have hf : c.l.isNone = false := Bool.eq_false_of_not_eq_true h
      simp only [step, hf, Bool.false_eq_true, ↓reduceIte])
    (by
      intro c h
      cases c with
      | mk label v work =>
        cases label with
        | none => rfl
        | some label => simp at h)
    fuel (pack (start cfg destination next answer)) (by
      rw [ht]
      simp only [pack, hh, Option.map_none, Option.isNone_none])
  rw [ht] at he
  refine ⟨used + 1, by omega, out, hh, hp, hi, hs, ?_⟩
  rw [run_add, he, pure_bind]
  simp only [run, step, pack, hh, Option.map_none, Option.isNone_none, ↓reduceIte, pure_bind]

/-- Every native answer reaches the actual resumed caller through physical
loading and the existing response program in this one call loop. -/
theorem received_run {s l m : Nat} (kind : OracleTapeDispatch.Kind)
    (cfg : BitOracleMachine.Config s l m) (request destination : Fin s) (next : Fin l)
    (oldPort : List Bool) (query : Tape (Option Bool)) (answer : List Bool) :
    let B := (cfg.stk destination).length + 3 * answer.length + 4
    ∃ after ≤ 3 * oldPort.length + 4 * answer.length + 8 +
        B * (6 * height (start cfg destination next answer).stk + 18 * B + 7),
      ∃ out : BitOraclePortTransfer.Config s l m,
        out.l = none ∧ project out = BitOracleMachine.resume cfg destination next answer ∧
        out.stk (.inr false) = [] ∧ out.stk (.inr true) = [] ∧
        run kind after (received cfg request destination next oldPort query answer) =
          pure (.done (pack out) query (wordTape answer)) := by
  dsimp only
  obtain ⟨a, ha, he⟩ := input_run kind cfg request destination next oldPort query answer
  obtain ⟨b, hb, out, hh, hp, hi, hs, ht⟩ := response_run kind cfg destination next answer query
  refine ⟨a + b, by omega, out, hh, hp, hi, hs, ?_⟩
  rw [run_add, he, pure_bind, ht]

/-- Specialize complete response execution to the actual hash reply state. -/
theorem answer_run {s l m : Nat} (kind : OracleTapeDispatch.Kind)
    (cfg : BitOracleMachine.Config s l m) (request destination : Fin s) (next : Fin l)
    (answer : List Bool) :
    let B := (cfg.stk destination).length + 3 * answer.length + 4
    ∃ after ≤ 3 * (cfg.stk request).length + 4 * answer.length + 8 +
        B * (6 * height (start cfg destination next answer).stk + 18 * B + 7),
      ∃ out : BitOraclePortTransfer.Config s l m,
        out.l = none ∧ project out = BitOracleMachine.resume cfg destination next answer ∧
        out.stk (.inr false) = [] ∧ out.stk (.inr true) = [] ∧
        run kind after (incoming cfg request destination next answer) =
          pure (.done (pack out) (wordTape (cfg.stk request)) (wordTape answer)) :=
  received_run kind cfg request destination next (cfg.stk request) (wordTape (cfg.stk request)) answer

/-- Coin dispatch uses its actual bit oracle and the same proved incoming loop. -/
theorem coin_issue {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (destination : Fin s) (next : Fin l) (query oldAnswer : Tape (Option Bool)) :
    step .coin (.issue destination (next, cfg.var)
      ⟨(pack (prepared cfg destination next [])).Tape, query, oldAnswer⟩) =
      (do let bit ← liftM (BitOracleMachine.spec.query .coin)
          pure (received cfg destination destination next [] query [bit])) := by
  simp only [step]
  rw [OracleTapeDispatch.coin_word]
  simp only [bind_assoc, pure_bind]
  rfl

/-- The native call starts from an actual TM1 request-preparation run, retaining
its saved finite continuation and complete work tape. -/
theorem hash_prepared_issue {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (request destination : Fin s) (next : Fin l) (oldPort previous : List Bool)
    (oldAnswer : Tape (Option Bool)) :
    let src := requestStart cfg request next oldPort
    let B := oldPort.length + 2 * (cfg.stk request).length + 4
    ∃ prep ≤ B * (6 * height src.stk + 18 * B + 7),
      let ready := (TM2TapeCost.tick (requestProgram request))^[prep] (pack src)
      ∃ before ≤ previous.length + 2 * (cfg.stk request).length + 5,
        run .hash before (.output destination ready.var.1
            ⟨.clear, ready.Tape, wordTape previous⟩ oldAnswer) =
          (do let answer ← liftM (BitOracleMachine.spec.query (.hash (cfg.stk request)))
              pure (incoming cfg request destination next answer)) := by
  dsimp only
  obtain ⟨prep, hp, he⟩ := BitOracleTapeCost.request_run cfg request next oldPort
  obtain ⟨before, hb, hr⟩ := hash_issue cfg request destination next previous oldAnswer
  refine ⟨prep, hp, before, hb, ?_⟩
  rw [he]
  exact hr

end ExplainableCrypto.Helios.Computational.BitOracleTapeCall
