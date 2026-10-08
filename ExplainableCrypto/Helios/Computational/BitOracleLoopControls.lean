import ExplainableCrypto.Helios.Computational.BitOracleLoopCorrespondence
import ExplainableCrypto.Helios.Computational.BitOracleCanary
import VCVio.OracleComp.SimSemantics.StateT.Basic

/-! Literal controls for the assembled loop and its costed tree correspondence. -/
namespace ExplainableCrypto.Helios.Computational.BitOracleLoopControls
open OracleComp OracleSpec BitOracleLoop BitOracleCanary

private structure Cache where
  entries : List (List Bool × List Bool) := []
  trace : List (List Bool × Bool) := []

private def handler : QueryImpl BitOracleMachine.spec (StateT Cache Id) := fun request state =>
  match request with
  | .coin => (true, state)
  | .hash word =>
    let prior := state.entries.lookup word
    let answer := prior.getD (true :: word)
    (answer, ⟨if prior.isSome then state.entries else (word, answer) :: state.entries,
      state.trace ++ [(word, prior.isSome)]⟩)

private def observe (fuel : Nat) (word : List Bool) (cache : Cache) :=
  let out := (simulateQ handler (run code fuel (.ready (initial word)))).run cache
  (match out.1 with
    | .ready cfg => some (cfg.l, cfg.stk 0, cfg.stk 1, cfg.stk 2, cfg.stk 3)
    | _ => none, out.2.trace)

/-- The general proof reaches the complete adaptive canary tree for every word. -/
theorem canary (word : List Bool) :
    Realizes code (source word) 0 (.ready (initial word)) := by
  rw [← BitOracleCanary.run_source]
  exact BitOracleLoop.run_source code 4 (initial word)

/-- Actual micro execution preserves two misses, a repeat hit and every final word. -/
theorem miss_miss_hit :
    observe 63 [false] {} =
      (some (none, [false], [true, false], [true, true, false], [true, false]),
        [([false], false), ([true, false], false), ([false], true)]) := by
  rfl

/-- A cache hit changes the next request and the actual number of micro steps. -/
theorem occupied_changes_request :
    observe 52 [false] ⟨[([false], [true])], []⟩ =
      (some (none, [false], [true], [true, true], [true]),
        [([false], true), ([true], false), ([false], true)]) := by
  rfl

/-- At the issue boundary preparation has not yet made any oracle call. -/
theorem preparation_is_silent : observe 7 [false] {} = (none, []) := by rfl

/-- The next micro step makes exactly the prepared native request. -/
theorem native_event_follows_preparation :
    observe 8 [false] {} = (none, [([false], false)]) := by rfl

/-- Zero source charge cannot certify a changed terminal caller state. -/
theorem zero_charge_not_arbitrary :
    ¬ Realizes code (pure (initial [true], 0)) 0 (.ready (initial [false])) := by
  rintro ⟨used, hu, he⟩
  have hz : used = 0 := by omega
  subst used
  have impossible : initial [false] = initial [true] := by
    injection he with h
    injection h
  have tapes := congrArg (fun cfg => cfg.stk 0) impossible
  contradiction

end ExplainableCrypto.Helios.Computational.BitOracleLoopControls
