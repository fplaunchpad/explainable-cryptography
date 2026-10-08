import ExplainableCrypto.Helios.Computational.BitOraclePrimitiveCost
import ExplainableCrypto.Helios.Computational.BitOracleTapeLoop

/-! Primitive target of the existing oracle tape loop. The deterministic
regions use the pinned TM1-to-TM0 compiler; physical I/O and native dispatch
are the existing operations. Phase returns inspect only finite control. -/
namespace ExplainableCrypto.Helios.Computational.BitOraclePrimitiveLoop
open Turing OracleComp OracleSpec BitOraclePortTransfer OracleTapeOutput

abbrev PrimitiveConfig (K L V : Type) :=
  TM0.Cfg (TM2to1.Γ' K (fun _ => Bool))
    (Option (TM1.Stmt (TM2to1.Γ' K (fun _ => Bool))
      (TM2to1.Λ' K (fun _ => Bool) L V) V) × V)

abbrev ComputeConfig (s l m : Nat) := PrimitiveConfig (Ports s) Unit (Option (Fin l) × Fin m)
abbrev ResponseConfig (s l m : Nat) :=
  PrimitiveConfig (Ports s) BitPortTransfer.Label ((Fin l × Fin m) × Option Bool)

/-- The pinned primitive transition, without an irrelevant default-state
requirement on potentially empty memory types. It moves or writes one cell. -/
def primitiveTick {Γ L V : Type} [Inhabited Γ] (M : L → TM1.Stmt Γ L V)
    (cfg : TM0.Cfg Γ (Option (TM1.Stmt Γ L V) × V)) :
    TM0.Cfg Γ (Option (TM1.Stmt Γ L V) × V) :=
  match cfg.q.1 with
  | none => cfg
  | some q =>
    let out := TM1to0.trAux M cfg.Tape.1 q cfg.q.2
    ⟨out.1, match out.2 with
      | .move d => cfg.Tape.move d
      | .write bit => cfg.Tape.write bit⟩

/-- This wrapper is exactly the existing compiler tick; it adds no semantics. -/
theorem primitiveTick_eq {Γ L V : Type} [Inhabited Γ] [Inhabited L] [Inhabited V]
    (M : L → TM1.Stmt Γ L V) (cfg : TM0.Cfg Γ (TM1to0.Λ' M)) :
    primitiveTick M cfg = TM1PrimitiveCost.tick M cfg := by
  cases cfg with
  | mk control tape => cases control with
    | mk label memory => cases label <;> rfl

inductive State (s l m : Nat) where
  | ready (label : Option (Fin l)) (memory : Fin m) (tapes : OracleTapeDispatch.Tapes (Ports s))
  | compute (source : Fin l) (cfg : ComputeConfig s l m) (query answer : Tape (Option Bool))
  | prepare (request destination : Fin s) (cfg : ResponseConfig s l m)
      (query answer : Tape (Option Bool))
  | output (kind : OracleTapeDispatch.Kind) (destination : Fin s) (saved : Fin l × Fin m)
      (cfg : OracleTapeOutput.Config (Ports s)) (answer : Tape (Option Bool))
  | issue (kind : OracleTapeDispatch.Kind) (destination : Fin s) (saved : Fin l × Fin m)
      (tapes : OracleTapeDispatch.Tapes (Ports s))
  | input (destination : Fin s) (saved : Fin l × Fin m)
      (query : Tape (Option Bool)) (cfg : OracleTapeInput.Config (Ports s))
  | response (destination : Fin s) (cfg : ResponseConfig s l m) (query answer : Tape (Option Bool))

/-- Saved finite memory and existing tapes suffice at every region handoff.
Only the existing native dispatch reads/writes a whole oracle word. -/
def step {s l m : Nat} (code : BitOracleMachine.Code s l m) :
    State s l m → OracleComp BitOracleMachine.spec (State s l m)
  | .ready label memory tapes => match label with
    | none => pure (.ready none memory tapes)
    | some source => match code source with
      | .compute _ => pure (.compute source
          ⟨(some (TM2to1.tr (BitOracleTapeLoop.localProgram code source) (.normal ())),
            (label, memory)), tapes.work⟩ tapes.query tapes.answer)
      | .hash request destination next => pure (.prepare request destination
          ⟨(some (TM2to1.tr (requestProgram request) (.normal .clear)),
            ((next, memory), none)), tapes.work⟩ tapes.query tapes.answer)
      | .coin destination next => pure (.issue .coin destination (next, memory) tapes)
  | .compute source cfg query answer =>
      if cfg.q.1.isNone then pure (.ready cfg.q.2.1 cfg.q.2.2 ⟨cfg.Tape, query, answer⟩)
      else pure (.compute source (primitiveTick (TM2to1.tr (BitOracleTapeLoop.localProgram code source)) cfg)
        query answer)
  | .prepare request destination cfg query answer =>
      if cfg.q.1.isNone then pure (.output .hash destination cfg.q.2.1 ⟨.clear, cfg.Tape, query⟩ answer)
      else pure (.prepare request destination (primitiveTick (TM2to1.tr (requestProgram request)) cfg)
        query answer)
  | .output kind destination saved cfg answer =>
      if cfg.phase = .done then pure (.issue kind destination saved ⟨cfg.work, cfg.query, answer⟩)
      else pure (.output kind destination saved (OracleTapeOutput.step (.inr false) cfg) answer)
  | .issue kind destination saved tapes => do
      let reply ← OracleTapeDispatch.dispatch kind tapes
      pure (.input destination saved reply.query ⟨.seekWork, reply.work, reply.answer⟩)
  | .input destination saved query cfg =>
      if cfg.phase = .done then pure (.response destination
        ⟨(some (TM2to1.tr (program destination) (.normal .clear)), (saved, none)), cfg.work⟩
        query cfg.answer)
      else pure (.input destination saved query (OracleTapeInput.step (.inr false) cfg))
  | .response destination cfg query answer =>
      if cfg.q.1.isNone then pure (.ready (some cfg.q.2.1.1) cfg.q.2.1.2 ⟨cfg.Tape, query, answer⟩)
      else pure (.response destination (primitiveTick (TM2to1.tr (program destination)) cfg) query answer)

def run {s l m : Nat} (code : BitOracleMachine.Code s l m) : Nat → State s l m →
    OracleComp BitOracleMachine.spec (State s l m)
  | 0, cfg => pure cfg
  | n + 1, cfg => do
      let next ← step code cfg
      run code n next

theorem run_add {s l m : Nat} (code : BitOracleMachine.Code s l m) (a b : Nat) (cfg : State s l m) :
    run code (a + b) cfg = (run code a cfg >>= run code b) := by
  induction a generalizing cfg with
  | zero => simp [run]
  | succ a ih => simp [Nat.succ_add, run, ih, bind_assoc]

/-- Proof-side lowering changes the deterministic control representation;
it retains all tapes exactly, and flattens only the old pure call-return step. -/
def lower {s l m : Nat} (code : BitOracleMachine.Code s l m) : BitOracleTapeLoop.State s l m → State s l m
  | .ready label memory tapes => .ready label memory tapes
  | .compute source cfg query answer => .compute source
      (TM1to0.trCfg (TM2to1.tr (BitOracleTapeLoop.localProgram code source)) cfg) query answer
  | .prepare request destination cfg query answer => .prepare request destination
      (TM1to0.trCfg (TM2to1.tr (requestProgram request)) cfg) query answer
  | .call kind cfg => match cfg with
    | .output destination saved cfg answer => .output kind destination saved cfg answer
    | .issue destination saved tapes => .issue kind destination saved tapes
    | .input destination saved query cfg => .input destination saved query cfg
    | .response destination cfg query answer => .response destination
        (TM1to0.trCfg (TM2to1.tr (program destination)) cfg) query answer
    | .done cfg query answer => .ready (some cfg.var.1.1) cfg.var.1.2 ⟨cfg.Tape, query, answer⟩

end ExplainableCrypto.Helios.Computational.BitOraclePrimitiveLoop
