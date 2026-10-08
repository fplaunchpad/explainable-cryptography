import ExplainableCrypto.Helios.Computational.BitOracleCanary
import VCVio.OracleComp.SimSemantics.StateT.Basic

/-! Independent literal adaptive traces. The deterministic toy response table
is a control, not a hash implementation or a cryptographic assumption. -/
namespace ExplainableCrypto.Helios.Computational.BitOracleMachineControls
open OracleComp OracleSpec BitOracleMachine BitOracleCanary

private structure Cache where
  entries : List (List Bool × List Bool) := []
  trace : List (List Bool × Bool) := []

private def handler : QueryImpl spec (StateT Cache Id) := fun request state =>
  match request with
  | .coin => (true, state)
  | .hash word =>
    let prior := state.entries.lookup word
    let answer := prior.getD (true :: word)
    (answer, ⟨if prior.isSome then state.entries else (word, answer) :: state.entries,
      state.trace ++ [(word, prior.isSome)]⟩)

private def observe (fuel : Nat) (word : List Bool) (cache : Cache) :=
  let out := (simulateQ handler (run code fuel (initial word))).run cache
  (out.1.1.l, out.1.1.stk 0, out.1.1.stk 1, out.1.1.stk 2, out.1.1.stk 3,
    out.1.2, out.2.trace)

/-- Two distinct misses and a repeat hit, with all words and exact cost retained. -/
theorem miss_miss_hit :
    observe 4 [false] {} =
      (none, [false], [true, false], [true, true, false], [true, false], 15,
        [([false], false), ([true, false], false), ([false], true)]) := by
  unfold observe
  rw [run_source]
  rfl

/-- An occupied first entry changes the second request, not only the returned answer. -/
theorem occupied_changes_request :
    observe 4 [false] ⟨[([false], [true])], []⟩ =
      (none, [false], [true], [true, true], [true], 11,
        [([false], true), ([true], false), ([false], true)]) := by
  unfold observe
  rw [run_source]
  rfl

/-- Fuel exhaustion exposes a running configuration instead of claiming a halt. -/
theorem early_not_halted : (observe 2 [false] {}).1 = some 2 := by
  decide +kernel

/-- Replacing an occupied coin port charges erasure and the delivered bit. -/
theorem coin_overwrite :
    let cfg : Config 4 4 1 := ⟨some 0, 0, ![[false, false, false], [], [], []]⟩
    let out := (simulateQ handler (step (fun _ => .coin 0 1) cfg)).run {}
    out.1.1.stk 0 = [true] ∧ out.1.1.l = some 1 ∧ out.1.2 = 5 := by
  decide +kernel

/-- The ghost measure cannot omit the request or response transfers. -/
theorem transfer_costs_required :
    (observe 4 [false] {}).2.2.2.2.2.1 > 11 ∧
    (observe 4 [false] {}).2.2.2.2.2.1 > 8 := by
  rw [miss_miss_hit]
  decide +kernel

end ExplainableCrypto.Helios.Computational.BitOracleMachineControls
