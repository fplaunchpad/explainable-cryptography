import ExplainableCrypto.Helios.Computational.BitOracleBoundedCanary
import VCVio.OracleComp.SimSemantics.StateT.Basic

/-! Literal stateful controls and necessary-premise counterexamples for the
bounded loop. The response table is a toy oracle, not the cryptographic hash. -/
namespace ExplainableCrypto.Helios.Computational.BitOracleBoundedControls
open OracleComp OracleSpec BitOracleLoopBounded BitOracleCanary

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
  let out := (simulateQ handler (simulateQ (adapter 2)
    (BitOracleLoop.run code (11 * (4 + 2 * word.length + 4 * 2))
      (.ready (initial word))))).run cache
  (match out.1 with
    | .ready cfg => some (cfg.l, cfg.stk 0, cfg.stk 1, cfg.stk 2, cfg.stk 3)
    | _ => none, out.2.trace)

/-- One common clock preserves adaptive queries, repeat cache hits and all words. -/
theorem miss_miss_hit :
    observe [false] {} =
      (some (none, [false], [true, false], [true, true], [true, false]),
        [([false], false), ([true, false], false), ([false], true)]) := by
  unfold observe
  rw [BitOracleBoundedCanary.run_handler]
  rfl

/-- The same clock works when a prior cache entry shortens the first answer. -/
theorem occupied_changes_request :
    observe [false] ⟨[([false], ⟨[true], by decide⟩)], []⟩ =
      (some (none, [false], [true], [true, true], [true]),
        [([false], true), ([true], false), ([false], true)]) := by
  unfold observe
  rw [BitOracleBoundedCanary.run_handler]
  rfl

private def emptyHandler : QueryImpl (spec 0) (StateT Nat Id) := fun request count =>
  match request with
  | .coin => (⟨true, trivial⟩, count + 1)
  | .hash _ => (⟨[], Nat.zero_le _⟩, count + 1)

/-- A zero-width hash answer is allowed and still executes all three queries. -/
theorem zero_width :
    let out := (simulateQ emptyHandler (simulateQ (adapter 0)
      (BitOracleLoop.run code 66 (.ready (initial [false]))))).run 0
    (match out.1 with
      | .ready cfg => cfg.l = none ∧ cfg.stk 0 = [false] ∧ cfg.stk 1 = [] ∧
          cfg.stk 2 = [] ∧ cfg.stk 3 = []
      | _ => False) ∧ out.2 = 3 := by
  have h := BitOracleBoundedCanary.run_handler 0 [false] emptyHandler
  change simulateQ emptyHandler (simulateQ (adapter 0)
    (BitOracleLoop.run code 66 (.ready (initial [false])))) = _ at h
  rw [h]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

private def recordingHandler : QueryImpl (spec 0) (StateT (List (List Bool)) Id) :=
  fun request log => match request with
    | .coin => (⟨true, trivial⟩, log)
    | .hash word => (⟨[], Nat.zero_le _⟩, log ++ [word])

/-- Output restrictions do not reject or truncate a longer raw request. -/
theorem raw_request_retained :
    (simulateQ recordingHandler (adapter 0 (.hash [true, true, false]))).run [] =
      ([], [[true, true, false]]) := by rfl

private def spinning : BitOracleMachine.Code 1 1 1 := fun _ => .coin 0 0
private def start : BitOracleMachine.Config 1 1 1 := ⟨some 0, 0, fun _ => []⟩
private def countHandler : QueryImpl BitOracleMachine.spec (StateT Nat Id) := fun q count =>
  match q with
  | .coin => (true, count + 1)
  | .hash _ => ([], count + 1)

/-- Refuted shortcut: padding a running source boundary executes further queries. -/
theorem missing_halt_changes_trace :
    ((simulateQ countHandler (BitOracleMachine.run spinning 1 start)).run 0).2 = 1 ∧
    ((simulateQ countHandler (BitOracleLoop.run spinning 22 (.ready start))).run 0).2 = 3 := by
  decide +kernel

/-- The termination premise excludes that concrete counterexample. -/
theorem spinning_not_within : ¬ Within 0 2 (BitOracleMachine.run spinning 1 start) := by
  intro h
  have bad := h true trivial
  have impossible : (some (0 : Fin 1)) = none := bad.1
  cases impossible

/-- A permitted response must meet the declared size bound. -/
theorem oversized_not_allowed : ¬ Allowed 2 (.hash []) [true, false, true] := by
  change ¬ (3 ≤ 2)
  decide

end ExplainableCrypto.Helios.Computational.BitOracleBoundedControls
