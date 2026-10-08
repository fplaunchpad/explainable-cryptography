import ExplainableCrypto.Helios.Computational.BitOracleTapeBoundedCanary
import ExplainableCrypto.Helios.Computational.BitOracleBoundedControls
import VCVio.OracleComp.SimSemantics.StateT.Basic

/-! Source-derived common clocks, necessary growth/halting conditions, and
literal actual tape execution. The response table is a toy bounded oracle. -/
namespace ExplainableCrypto.Helios.Computational.OracleTapeBoundedControls
open Turing OracleComp OracleSpec TM2TapeRuns OracleTapeOutput BitOracleCanary
open BitOracleLoopBounded (adapter spec)
open BitOracleTapeLoop (observeCaller ready)

private structure Cache where
  entries : List (List Bool × {a : List Bool // a.length ≤ 2}) := []
  trace : List (List Bool × Bool) := []

private def handler : QueryImpl (spec 2) (StateT Cache Id) := fun request state =>
  match request with
  | .coin => (⟨true, trivial⟩, state)
  | .hash word =>
    let prior := state.entries.lookup word
    let fallback : {a : List Bool // a.length ≤ 2} :=
      ⟨(true :: word).take 2, by simp only [List.length_take]; exact Nat.min_le_left _ _⟩
    let answer := prior.getD fallback
    (answer, ⟨if prior.isSome then state.entries else (word, answer) :: state.entries,
      state.trace ++ [(word, prior.isSome)]⟩)

private def observe (word : List Bool) (cache : Cache) :=
  let out := (observeCaller <$> simulateQ handler (simulateQ (adapter 2)
    (BitOracleTapeLoop.run code (BitOracleTapeBoundedCanary.clock 2 word [true, true, false, false])
      (ready (initial word) (wordTape [true, true, false, false]) (wordTape [false]))))).run cache
  (out.1.map (fun cfg => (cfg.l, cfg.stk 0, cfg.stk 1, cfg.stk 2, cfg.stk 3)), out.2.trace)

/-- A derived common tape clock preserves adaptive misses, a repeat hit and all caller words. -/
theorem miss_miss_hit :
    observe [false] {} =
      (some (none, [false], [true, false], [true, true], [true, false]),
        [([false], false), ([true, false], false), ([false], true)]) := by
  unfold observe
  rw [BitOracleTapeBoundedCanary.run_handler]
  rfl

/-- The same clock works when a cached shorter answer changes the next request. -/
theorem occupied_changes_request :
    observe [false] ⟨[([false], ⟨[true], by decide⟩)], []⟩ =
      (some (none, [false], [true], [true, true], [true]),
        [([false], true), ([true], false), ([false], true)]) := by
  unfold observe
  rw [BitOracleTapeBoundedCanary.run_handler]
  rfl

private def emptyHandler : QueryImpl (spec 0) (StateT Nat Id) := fun request count =>
  match request with
  | .coin => (⟨true, trivial⟩, count + 1)
  | .hash _ => (⟨[], Nat.zero_le _⟩, count + 1)

/-- Zero-width answers still execute all three queries and preserve the entire caller. -/
theorem zero_width :
    let out := (observeCaller <$> simulateQ emptyHandler (simulateQ (adapter 0)
      (BitOracleTapeLoop.run code (BitOracleTapeBoundedCanary.clock 0 [false] [true, false])
        (ready (initial [false]) (wordTape [true, false]) (wordTape [true]))))).run 0
    out.1 = some (final [false] [] [] []) ∧ out.2 = 3 := by
  rw [BitOracleTapeBoundedCanary.run_handler]
  exact ⟨rfl, rfl⟩

private def emptyCaller : BitOracleMachine.Config 1 1 1 := ⟨some 0, 0, fun _ => []⟩

/-- Keeping only the initial height is false even for one concrete native reply. -/
theorem frozen_height_fails :
    height emptyCaller.stk = 0 ∧
    height (BitOracleMachine.resume emptyCaller 0 0 [true]).stk = 1 ∧
    ¬ height (BitOracleMachine.resume emptyCaller 0 0 [true]).stk ≤ height emptyCaller.stk := by
  decide +kernel

/-- Empty input still needs dispatch, actual halt and return; zero ticks remain live. -/
theorem empty_halt_needs_steps :
    observeCaller <$> BitOracleTapeLoop.run (fun _ => .compute .halt) 3
      (ready emptyCaller (wordTape []) (wordTape [])) =
        (pure (some {emptyCaller with l := none}) : OracleComp BitOracleMachine.spec _) ∧
    (observeCaller (ready emptyCaller (wordTape []) (wordTape []))).map (fun c => c.l) = some (some 0) := by
  exact ⟨rfl, rfl⟩

private def spinning : BitOracleMachine.Code 1 1 1 := fun _ => .coin 0 0
private def countHandler : QueryImpl BitOracleMachine.spec (StateT Nat Id) := fun q count =>
  match q with
  | .coin => (true, count + 1)
  | .hash _ => ([], count + 1)

/-- Padding a live source boundary makes additional actual tape-loop queries. -/
theorem live_padding_adds_queries :
    ((simulateQ countHandler (BitOracleMachine.run spinning 1 emptyCaller)).run 0).2 = 1 ∧
    1 < ((simulateQ countHandler (BitOracleTapeLoop.run spinning 2000
      (ready emptyCaller (wordTape []) (wordTape [])))).run 0).2 := by decide +kernel

end ExplainableCrypto.Helios.Computational.OracleTapeBoundedControls
