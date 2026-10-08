import ExplainableCrypto.Helios.Computational.BitOracleTapeCompute
import ExplainableCrypto.Helios.Computational.BitOracleTapeCall

/-! A source-program tape loop. Only finite control is saved at dispatch;
work and native tapes persist through computation and every oracle call. -/
namespace ExplainableCrypto.Helios.Computational.BitOracleTapeLoop
open Turing OracleComp OracleSpec TM2TapeRuns BitOraclePortTransfer OracleTapeOutput

inductive State (s l m : Nat) where
  | ready (label : Option (Fin l)) (memory : Fin m) (tapes : OracleTapeDispatch.Tapes (Ports s))
  | compute (source : Fin l) (cfg : BitOracleTapeCompute.Config s l m)
      (query answer : Tape (Option Bool))
  | prepare (request destination : Fin s) (cfg : BitOracleTapeCall.ResponseConfig s l m)
      (query answer : Tape (Option Bool))
  | call (kind : OracleTapeDispatch.Kind) (cfg : BitOracleTapeCall.State s l m)

/-- The fixed ordinary-region program selected by the source label. -/
def localProgram {s l m : Nat} (code : BitOracleMachine.Code s l m) (source : Fin l) :
    Unit → TM2.Stmt (fun _ : Ports s => Bool) Unit (Option (Fin l) × Fin m) := fun _ =>
  match code source with
  | .compute q => BitOracleTapeCompute.compile q
  | _ => .halt

/-- Native calls use the existing call transitions. Return changes finite
control only; no tape is decoded, repacked or copied at a boundary. -/
def step {s l m : Nat} (code : BitOracleMachine.Code s l m) :
    State s l m → OracleComp BitOracleMachine.spec (State s l m)
  | .ready label memory tapes => match label with
    | none => pure (.ready none memory tapes)
    | some source => match code source with
      | .compute _ => pure (.compute source
          ⟨some (.normal ()), (label, memory), tapes.work⟩ tapes.query tapes.answer)
      | .hash request destination next => pure (.prepare request destination
          ⟨some (.normal .clear), ((next, memory), none), tapes.work⟩ tapes.query tapes.answer)
      | .coin destination next => pure (.call .coin (.issue destination (next, memory) tapes))
  | .compute source cfg query answer =>
      if cfg.l.isNone then pure (.ready cfg.var.1 cfg.var.2 ⟨cfg.Tape, query, answer⟩)
      else pure (.compute source (TM2TapeCost.tick (localProgram code source) cfg) query answer)
  | .prepare request destination cfg query answer =>
      if cfg.l.isNone then pure (.call .hash (.output destination cfg.var.1
        ⟨.clear, cfg.Tape, query⟩ answer))
      else pure (.prepare request destination (TM2TapeCost.tick (requestProgram request) cfg) query answer)
  | .call _ (.done cfg query answer) =>
      pure (.ready (some cfg.var.1.1) cfg.var.1.2 ⟨cfg.Tape, query, answer⟩)
  | .call kind cfg => State.call kind <$> BitOracleTapeCall.step kind cfg

def run {s l m : Nat} (code : BitOracleMachine.Code s l m) :
    Nat → State s l m → OracleComp BitOracleMachine.spec (State s l m)
  | 0, cfg => pure cfg
  | n + 1, cfg => do
      let next ← step code cfg
      run code n next

theorem run_add {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (a b : Nat) (cfg : State s l m) :
    run code (a + b) cfg = (run code a cfg >>= run code b) := by
  induction a generalizing cfg with
  | zero => simp [run]
  | succ a ih => simp [Nat.succ_add, run, ih, bind_assoc]

/-- Proof-only source presentation. Actual dispatch retains the existing tape. -/
def ready {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (query answer : Tape (Option Bool)) : State s l m :=
  .ready cfg.l cfg.var ⟨(pack (BitOracleTapeCompute.framed cfg)).Tape, query, answer⟩

private theorem phase_run {s l m : Nat} {A : Type} (code : BitOracleMachine.Code s l m)
    (f : A → A) (finished : A → Prop) [DecidablePred finished]
    (embed : A → State s l m)
    (hs : ∀ a, ¬ finished a → step code (embed a) = pure (embed (f a)))
    (hf : ∀ a, finished a → f a = a)
    (fuel : Nat) (a : A) (ha : finished (f^[fuel] a)) :
    ∃ used ≤ fuel, run code used (embed a) = pure (embed (f^[fuel] a)) := by
  induction fuel generalizing a with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ fuel ih =>
    by_cases h : finished a
    · exact ⟨0, Nat.zero_le _, by rw [Function.iterate_fixed (hf a h)]; rfl⟩
    · rw [Function.iterate_succ_apply] at ha
      obtain ⟨used, hu, he⟩ := ih _ ha
      refine ⟨used + 1, by omega, ?_⟩
      rw [run, hs a h, pure_bind, he, Function.iterate_succ_apply]

/-- Every ordinary source statement returns to the actual loop with its exact
new caller and both native tapes retained, in a derived number of tape ticks. -/
theorem compute_run {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (cfg : BitOracleMachine.Config s l m) (source : Fin l)
    (q : TM2.Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m))
    (hl : cfg.l = some source) (hc : code source = .compute q)
    (query answer : Tape (Option Bool)) :
    let a := TM2TapeCost.accesses q
    let H := height (BitOracleTapeCompute.framed cfg).stk
    ∃ used ≤ 3 + a * (2 * (H + a) + 2),
      run code used (ready cfg query answer) =
        pure (ready (TM2.stepAux q cfg.var cfg.stk) query answer) := by
  dsimp only
  obtain ⟨fuel, hf, he⟩ := BitOracleTapeCompute.run q cfg
  have lp : localProgram code source = fun _ : Unit => BitOracleTapeCompute.compile q := by
    funext u
    simp [localProgram, hc]
  obtain ⟨used, hu, hr⟩ := phase_run code (TM2TapeCost.tick (localProgram code source))
    (fun c => c.l.isNone = true) (fun c => State.compute source c query answer)
    (by
      intro c h
      have hf : c.l.isNone = false := Bool.eq_false_of_not_eq_true h
      simp only [step, hf, Bool.false_eq_true, ↓reduceIte])
    (by
      intro c h
      cases c with
      | mk label v tape => cases label <;> simp_all [TM2TapeCost.tick, TM1.step])
    fuel (pack (BitOracleTapeCompute.entry cfg)) (by
      rw [lp, he]
      rfl)
  rw [lp, he] at hr
  refine ⟨1 + (used + 1), by omega, ?_⟩
  have initial : run code 1 (ready cfg query answer) =
      pure (.compute source (pack (BitOracleTapeCompute.entry cfg)) query answer) := by
    simp only [run, ready, step, hl, hc, bind_pure]
    simp only [BitOracleTapeCompute.entry, pack, hl, Option.map_some]
  rw [run_add, initial, pure_bind, run_add, hr, pure_bind]
  rfl

private theorem call_done {s l m : Nat} (kind : OracleTapeDispatch.Kind)
    (fuel : Nat) (cfg : BitOracleTapeCall.ResponseConfig s l m) (query answer : Tape (Option Bool)) :
    BitOracleTapeCall.run kind fuel (.done cfg query answer) = pure (.done cfg query answer) := by
  induction fuel <;> simp_all [BitOracleTapeCall.run, BitOracleTapeCall.step]

/-- Lift a checked pure call region into the surrounding source loop, stopping
before its return transition. No new stack/tape execution proof is required. -/
private theorem call_pure_run {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (kind : OracleTapeDispatch.Kind) (fuel : Nat) (cfg out : BitOracleTapeCall.State s l m)
    (he : BitOracleTapeCall.run kind fuel cfg = pure out) :
    ∃ used ≤ fuel, run code used (.call kind cfg) = pure (.call kind out) := by
  induction fuel generalizing cfg out with
  | zero =>
    have h : cfg = out := by injection he
    subst out
    exact ⟨0, le_rfl, rfl⟩
  | succ fuel ih =>
    by_cases done : ∃ c q a, cfg = .done c q a
    · obtain ⟨c, q, a, rfl⟩ := done
      rw [call_done] at he
      have h : BitOracleTapeCall.State.done c q a = out := by injection he
      subst out
      exact ⟨0, Nat.zero_le _, rfl⟩
    · have hs : step code (.call kind cfg) = State.call kind <$> BitOracleTapeCall.step kind cfg := by
        cases cfg <;> simp_all [step]
      cases h : BitOracleTapeCall.step kind cfg with
      | pure mid =>
        change BitOracleTapeCall.step kind cfg = pure mid at h
        rw [BitOracleTapeCall.run, h, pure_bind] at he
        obtain ⟨used, hu, hr⟩ := ih mid out he
        refine ⟨used + 1, by omega, ?_⟩
        rw [run, hs, h, map_pure, pure_bind, hr]
      | queryBind q next =>
        change BitOracleTapeCall.step kind cfg = OracleComp.queryBind q next at h
        rw [BitOracleTapeCall.run, h] at he
        cases he

private theorem request_tape {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (request : Fin s) (next : Fin l) :
    (pack (requestStart cfg request next [])).Tape =
      (pack (BitOracleTapeCompute.framed cfg)).Tape := by
  have words : (requestStart cfg request next []).stk = (BitOracleTapeCompute.framed cfg).stk := by
    funext port
    cases port with
    | inl i => exact (request_start cfg request i next []).1
    | inr bit => cases bit <;> rfl
  simp only [pack, words]

private theorem resumed {s l m : Nat} (out : BitOraclePortTransfer.Config s l m)
    (cfg : BitOracleMachine.Config s l m) (hp : project out = cfg)
    (hi : out.stk (.inr false) = []) (hs : out.stk (.inr true) = [])
    (query answer : Tape (Option Bool)) :
    State.ready (some out.var.1.1) out.var.1.2 ⟨(pack out).Tape, query, answer⟩ =
      ready cfg query answer := by
  subst cfg
  have words : out.stk = (BitOracleTapeCompute.framed (project out)).stk := by
    funext port
    cases port with
    | inl i => rfl
    | inr bit => cases bit <;> assumption
  simp only [ready, pack, words]
  rfl

/-- Every native reply completes in the surrounding source loop, including the
return dispatch. Canonical ready presentation and private emptiness are derived. -/
theorem reply_run {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (kind : OracleTapeDispatch.Kind) (cfg : BitOracleMachine.Config s l m)
    (request destination : Fin s) (next : Fin l) (oldPort : List Bool)
    (query : Tape (Option Bool)) (answer : List Bool) :
    let B := (cfg.stk destination).length + 3 * answer.length + 4
    ∃ used ≤ 3 * oldPort.length + 4 * answer.length + 9 +
        B * (6 * height (start cfg destination next answer).stk + 18 * B + 7),
      run code used (.call kind (BitOracleTapeCall.received cfg request destination next oldPort query answer)) =
        pure (ready (BitOracleMachine.resume cfg destination next answer) query (wordTape answer)) := by
  dsimp only
  obtain ⟨fuel, hf, out, hh, hp, hi, hs, he⟩ :=
    BitOracleTapeCall.received_run kind cfg request destination next oldPort query answer
  obtain ⟨used, hu, hr⟩ := call_pure_run code kind fuel _ _ he
  refine ⟨used + 1, by omega, ?_⟩
  rw [run_add, hr, pure_bind]
  simp only [run, step, pure_bind]
  exact congrArg pure (resumed out _ hp hi hs query (wordTape answer))

private theorem prepare_run {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (cfg : BitOracleMachine.Config s l m) (request destination : Fin s) (next : Fin l)
    (previous : List Bool) (oldAnswer : Tape (Option Bool)) :
    let B := 2 * (cfg.stk request).length + 4
    ∃ used ≤ B * (6 * height (requestStart cfg request next []).stk + 18 * B + 7) + 1,
      run code used (.prepare request destination (pack (requestStart cfg request next []))
        (wordTape previous) oldAnswer) =
        pure (.call .hash (BitOracleTapeCall.begin cfg request destination next previous oldAnswer)) := by
  dsimp only
  obtain ⟨fuel, hf, he⟩ := BitOracleTapeCost.request_run cfg request next []
  obtain ⟨used, hu, hr⟩ := phase_run code (TM2TapeCost.tick (requestProgram request))
    (fun c => c.l.isNone = true)
    (fun c => State.prepare request destination c (wordTape previous) oldAnswer)
    (by
      intro c h
      have hf : c.l.isNone = false := Bool.eq_false_of_not_eq_true h
      simp only [step, hf, Bool.false_eq_true, ↓reduceIte])
    (by
      intro c h
      cases c with
      | mk label v tape => cases label <;> simp_all [TM2TapeCost.tick, TM1.step])
    fuel (pack (requestStart cfg request next [])) (by rw [he]; rfl)
  rw [he] at hr
  refine ⟨used + 1, by simp only [List.length_nil, Nat.zero_add] at hf; omega, ?_⟩
  rw [run_add, hr, pure_bind]
  rfl

private theorem export_issue {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (cfg : BitOracleMachine.Config s l m) (request destination : Fin s) (next : Fin l)
    (previous : List Bool) (oldAnswer : Tape (Option Bool)) :
    ∃ used ≤ previous.length + 2 * (cfg.stk request).length + 5,
      run code used (.call .hash (BitOracleTapeCall.begin cfg request destination next previous oldAnswer)) =
        (do let answer ← liftM (BitOracleMachine.spec.query (.hash (cfg.stk request)))
            pure (.call .hash (BitOracleTapeCall.incoming cfg request destination next answer))) := by
  obtain ⟨fuel, hf, he⟩ := BitOracleTapeCall.export_run .hash cfg request destination next previous oldAnswer
  obtain ⟨used, hu, hr⟩ := call_pure_run code .hash fuel _ _ he
  refine ⟨used + 1, by omega, ?_⟩
  rw [run_add, hr, pure_bind]
  simp only [run, step, BitOracleTapeCall.step]
  rw [OracleTapeDispatch.hash_word]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  rfl

/-- Source dispatch, actual preparation and physical export issue exactly the
source hash request in the surrounding loop, before its answer is chosen. -/
theorem hash_issue {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (cfg : BitOracleMachine.Config s l m) (source : Fin l)
    (request destination : Fin s) (next : Fin l)
    (hl : cfg.l = some source) (hc : code source = .hash request destination next)
    (previous : List Bool) (oldAnswer : Tape (Option Bool)) :
    let B := 2 * (cfg.stk request).length + 4
    ∃ used ≤ B * (6 * height (requestStart cfg request next []).stk + 18 * B + 7) +
        previous.length + 2 * (cfg.stk request).length + 7,
      run code used (ready cfg (wordTape previous) oldAnswer) =
        (do let answer ← liftM (BitOracleMachine.spec.query (.hash (cfg.stk request)))
            pure (.call .hash (BitOracleTapeCall.incoming cfg request destination next answer))) := by
  dsimp only
  obtain ⟨a, ha, he⟩ := prepare_run code cfg request destination next previous oldAnswer
  obtain ⟨b, hb, hr⟩ := export_issue code cfg request destination next previous oldAnswer
  have initial : run code 1 (ready cfg (wordTape previous) oldAnswer) =
      pure (.prepare request destination (pack (requestStart cfg request next []))
        (wordTape previous) oldAnswer) := by
    simp only [run, ready, step, hl, hc, bind_pure]
    rw [← request_tape cfg request next]
    rfl
  refine ⟨1 + (a + b), by omega, ?_⟩
  rw [run_add, initial, pure_bind, run_add, he, pure_bind, hr]

/-- Coin dispatch uses the actual native bit event and preserves the unused
query tape. Its response state is the input of the general reply theorem. -/
theorem coin_issue {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (cfg : BitOracleMachine.Config s l m) (source : Fin l) (destination : Fin s) (next : Fin l)
    (hl : cfg.l = some source) (hc : code source = .coin destination next)
    (query oldAnswer : Tape (Option Bool)) :
    run code 2 (ready cfg query oldAnswer) =
      (do let bit ← liftM (BitOracleMachine.spec.query .coin)
          pure (.call .coin (BitOracleTapeCall.received cfg destination destination next [] query [bit]))) := by
  have initial : run code 1 (ready cfg query oldAnswer) =
      pure (.call .coin (.issue destination (next, cfg.var)
        ⟨(pack (BitOracleTapeCall.prepared cfg destination next [])).Tape, query, oldAnswer⟩)) := by
    simp only [run, ready, step, hl, hc, bind_pure]
    rw [← request_tape cfg destination next]
    rfl
  change run code (1 + 1) (ready cfg query oldAnswer) = _
  rw [run_add, initial, pure_bind]
  simp only [run, step]
  rw [BitOracleTapeCall.coin_issue]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  rfl

end ExplainableCrypto.Helios.Computational.BitOracleTapeLoop
