import ExplainableCrypto.Helios.Computational.BitOracleTapeCorrespondence
import VCVio.OracleComp.SimSemantics.StateT.Basic
import Mathlib.Data.Fin.VecNotation

/-! Source and actual tape-loop controls, with independently specified complete
caller words, finite return context and native query/cache traces. -/
namespace ExplainableCrypto.Helios.Computational.OracleTapeLoopControls
open Turing OracleComp OracleSpec BitOracleTapeLoop OracleTapeOutput OracleTapeDispatch

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

private def initial (word : List Bool) : BitOracleMachine.Config 4 6 2 :=
  ⟨some 0, 0, ![word, [], [], [false, true]]⟩

private def code : BitOracleMachine.Code 4 6 2 := fun label => match label.val with
  | 0 => .compute (.push 0 (fun _ => true) (.goto (fun _ => 1)))
  | 1 => .hash 0 1 2
  | 2 => .compute (.pop 3 (fun _ _ => 1) (.goto (fun _ => 3)))
  | 3 => .hash 1 2 4
  | 4 => .hash 0 3 5
  | _ => .compute .halt

private def column (port : BitOraclePortTransfer.Ports 4)
    (tape : WorkTape (BitOraclePortTransfer.Ports 4)) : List Bool :=
  (readWord (tape.map ⟨fun cell => cell.2 port, rfl⟩)).reverse

private structure View where
  label : Option Nat
  memory : Nat
  bottom : Bool
  first : List Bool
  second : List Bool
  third : List Bool
  fourth : List Bool
  input : List Bool
  scratch : List Bool
  query : List Bool
  answer : List Bool
  deriving DecidableEq

private def observe (program : BitOracleMachine.Code 4 6 2) (fuel : Nat) (cache : Cache) :
    Option View × List (BitOracleMachine.Request × Bool) :=
  let out := (simulateQ handler (run program fuel
    (ready (initial [false]) (wordTape [true, true, false, false]) (wordTape [false])))).run cache
  (match out.1 with
    | .ready label memory tapes => some ⟨label.map Fin.val, memory.val, tapes.work.head.1,
        column (.inl 0) tapes.work, column (.inl 1) tapes.work,
        column (.inl 2) tapes.work, column (.inl 3) tapes.work,
        column (.inr false) tapes.work, column (.inr true) tapes.work,
        readWord tapes.query, readWord tapes.answer⟩
    | _ => none, out.2.trace)

/-- The general theorem covers the mixed adaptive source for every initial word. -/
theorem derived_source (word : List Bool) :
    Realizes code (Prod.fst <$> BitOracleMachine.run code 6 (initial word))
      (ready (initial word) (wordTape [true, true, false, false]) (wordTape [false])) :=
  run_source code 6 (initial word) _ _

/-- Independently specified source behavior includes three calls and two local updates. -/
theorem source_control :
    let out := (simulateQ handler (BitOracleMachine.run code 6 (initial [false]))).run {}
    (out.1.1.l, out.1.1.var.val, out.1.1.stk 0, out.1.1.stk 1, out.1.1.stk 2,
      out.1.1.stk 3, out.2.trace) =
      (none, 1, [true, false], [true, true, false], [true, true, true, false],
        [true, true, false], [(.hash [true, false], false),
          (.hash [true, true, false], false), (.hash [true, false], true)]) := by rfl

/-- Actual tape execution retains all caller/private words and both native tapes. -/
theorem mixed_run :
    observe code 1024 {} =
      (some ⟨none, 1, true, [true, false], [true, true, false], [true, true, true, false],
        [true, true, false], [], [], [true, false], [true, true, false]⟩,
        [(.hash [true, false], false), (.hash [true, true, false], false),
          (.hash [true, false], true)]) := by decide +kernel

/-- An occupied cache changes the adaptive second request and complete returned words. -/
theorem occupied_run :
    observe code 1024 ⟨[([true, false], [false])], []⟩ =
      (some ⟨none, 1, true, [true, false], [false], [true, false], [false],
        [], [], [true, false], [false]⟩,
        [(.hash [true, false], true), (.hash [false], false),
          (.hash [true, false], true)]) := by decide +kernel

/-- A source port can also be its destination; every other caller word survives. -/
theorem aliased_run :
    observe (fun label => if label = 0 then .hash 0 0 1 else .compute .halt) 512 {} =
      (some ⟨none, 0, true, [true, false], [], [], [false, true],
        [], [], [false], [true, false]⟩, [(.hash [false], false)]) := by decide +kernel

/-- Coin dispatch and the following ordinary halt preserve the unused query tape. -/
theorem coin_run :
    observe (fun label => if label = 0 then .coin 0 1 else .compute .halt) 512 {} =
      (some ⟨none, 0, true, [true], [], [], [false, true],
        [], [], [true, true, false, false], [true]⟩, [(.coin, false)]) := by decide +kernel

/-- Treating every return as a source halt loses the actual goto continuation. -/
theorem goto_not_halt :
    (TM2.stepAux (BitOracleTapeCompute.compile (.goto (fun _ : Fin 2 => (1 : Fin 6))))
      ((initial []).l, (initial []).var) (BitOracleTapeCompute.framed (initial [])).stk).var.1 = some 1 ∧
    (some (1 : Fin 6)) ≠ none := by decide +kernel

/-- Retaining the entry label on halt spuriously resumes an already halted caller. -/
theorem halt_clears_label :
    (TM2.stepAux (BitOracleTapeCompute.compile (s := 4) (l := 6) (m := 2) .halt)
      ((initial []).l, (initial []).var) (BitOracleTapeCompute.framed (initial [])).stk).var.1 = none ∧
    (initial []).l ≠ none := by decide +kernel

end ExplainableCrypto.Helios.Computational.OracleTapeLoopControls
