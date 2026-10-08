import ExplainableCrypto.Helios.Computational.BitOracleTapeCall
import VCVio.OracleComp.SimSemantics.StateT.Basic
import Mathlib.Data.Fin.VecNotation

/-! Native-event and complete physical-call controls. Expected words and
cache traces come from the literal source interaction, not the tape interpreter. -/
namespace ExplainableCrypto.Helios.Computational.OracleTapeCallControls
open Turing OracleComp OracleSpec BitOracleTapeCall OracleTapeOutput OracleTapeDispatch

private structure Cache where
  entries : List (List Bool × List Bool) := []
  trace : List (BitOracleMachine.Request × Bool) := []

private def handler : QueryImpl BitOracleMachine.spec (StateT Cache Id) := fun request state =>
  match request with
  | .coin => (true, {state with trace := state.trace ++ [(.coin, false)]})
  | .hash word =>
    let prior := state.entries.lookup word
    let answer := prior.getD (true :: word)
    (answer, ⟨if prior.isSome then state.entries else (word, answer) :: state.entries,
      state.trace ++ [(.hash word, prior.isSome)]⟩)

private def src : BitOracleMachine.Config 2 2 1 := ⟨some 0, 0, ![[false], [true, true]]⟩
private def initial : State 2 2 1 := begin src 0 1 1 [true, false, false] (wordTape [false, true])

private structure View where
  halted : Bool
  next : Nat
  memory : Nat
  bottom : Bool
  source : Option Bool
  destination : Option Bool
  nextDestination : Option Bool
  endDestination : Option Bool
  input : Option Bool
  scratch : Option Bool
  query : List Bool
  answer : List Bool
  deriving DecidableEq

private def observe (kind : Kind) (fuel : Nat) (state : State 2 2 1) (cache : Cache) :
    Option View × List (BitOracleMachine.Request × Bool) :=
  let out := (simulateQ handler (run kind fuel state)).run cache
  (match out.1 with
    | .done cfg query answer => some
        ⟨cfg.l.isNone, cfg.var.1.1.val, cfg.var.1.2.val, cfg.Tape.head.1,
          cfg.Tape.head.2 (.inl 0), cfg.Tape.head.2 (.inl 1),
          (cfg.Tape.move .right).head.2 (.inl 1),
          ((Tape.move .right)^[2] cfg.Tape).head.2 (.inl 1),
          cfg.Tape.head.2 (.inr false), cfg.Tape.head.2 (.inr true),
          readWord query, readWord answer⟩
    | _ => none, out.2.trace)

/-- Apply the source-derived preparation theorem with an occupied private port. -/
theorem derived_issue :
    let start := BitOraclePortTransfer.requestStart src 0 1 [true, true]
    ∃ prep ≤ 8 * (6 * TM2TapeRuns.height start.stk + 18 * 8 + 7),
      let ready := (TM2TapeCost.tick (BitOraclePortTransfer.requestProgram 0))^[prep]
        (TM2TapeRuns.pack start)
      ∃ before ≤ 10,
        run .hash before (.output 1 ready.var.1
          ⟨.clear, ready.Tape, wordTape [true, false, false]⟩ (wordTape [false, true])) =
          (do let answer ← liftM (BitOracleMachine.spec.query (.hash [false]))
              pure (incoming src 0 1 1 answer)) := by
  exact hash_prepared_issue src 0 1 1 [true, true] [true, false, false] (wordTape [false, true])

/-- Export and its handoff are silent even with stale native words present. -/
theorem preparation_silent : observe .hash 9 initial {} = (none, []) := by rfl

/-- The next transition issues exactly the selected source word. -/
theorem native_event :
    observe .hash 10 initial {} = (none, [(.hash [false], false)]) := by rfl

/-- The actual loop returns the answer, caller continuation and clean workspace. -/
theorem hash_call :
    observe .hash 128 initial {} =
      (some ⟨true, 1, 0, true, some false, some false, some true, none,
        none, none, [false], [true, false]⟩, [(.hash [false], false)]) := by rfl

/-- A cached longer answer is loaded and copied in full, retaining its hit trace. -/
theorem occupied_reply :
    observe .hash 192 initial ⟨[([false], [false, false, true])], []⟩ =
      (some ⟨true, 1, 0, true, some false, some true, some false, some false,
        none, none, [false], [false, false, true]⟩, [(.hash [false], true)]) := by decide +kernel

private def coinInitial : State 2 2 1 := .issue 1 (1, 0)
  ⟨(TM2TapeRuns.pack (prepared src 1 1 [])).Tape, wordTape [false, true], wordTape [false]⟩

/-- Coin uses the actual bit event and retains the unused query tape. -/
theorem coin_call :
    observe .coin 64 coinInitial {} =
      (some ⟨true, 1, 0, true, some false, some true, none, none,
        none, none, [false, true], [true]⟩, [(.coin, false)]) := by rfl

/-- A blank terminates a native word; filtering blanks would issue another query. -/
theorem blank_terminates :
    readWord (Tape.mk' ∅ (ListBlank.mk [some true, none, some false])) = [true] ∧
    readWord (wordTape [true, false]) ≠ [true] := by decide +kernel

end ExplainableCrypto.Helios.Computational.OracleTapeCallControls
