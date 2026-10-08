import ExplainableCrypto.Helios.Computational.BitOraclePrimitiveCanary
import ExplainableCrypto.Helios.Computational.BitOraclePrimitiveFinite
import ExplainableCrypto.Helios.Computational.OracleTapeBoundedControls
import ExplainableCrypto.Helios.Computational.BitOracleBoundedControls
import VCVio.OracleComp.SimSemantics.StateT.Basic

/-! Source-derived common clocks, necessary growth/halting conditions, and
literal actual tape execution. The response table is a toy bounded oracle. -/
namespace ExplainableCrypto.Helios.Computational.OraclePrimitiveContractControls
open Turing OracleComp OracleSpec TM2TapeRuns OracleTapeOutput BitOracleCanary
open BitOracleLoopBounded (adapter spec)
open BitOraclePrimitiveBounded (observe)
open BitOraclePrimitiveLoop (lower)
open BitOracleTapeLoop (ready)

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

private noncomputable def observeCache (word : List Bool) (cache : Cache) :=
  let out := (observe <$> simulateQ handler (simulateQ (adapter 2)
    (BitOraclePrimitiveLoop.run code (BitOraclePrimitiveCanary.clock 2 word [true, true, false, false])
      (lower code (ready (initial word) (wordTape [true, true, false, false]) (wordTape [false])))))).run cache
  (out.1.map (fun cfg => (cfg.l, cfg.stk 0, cfg.stk 1, cfg.stk 2, cfg.stk 3)), out.2.trace)

/-- A derived common primitive clock preserves adaptive misses, a repeat hit and all caller words. -/
theorem miss_miss_hit :
    observeCache [false] {} =
      (some (none, [false], [true, false], [true, true], [true, false]),
        [([false], false), ([true, false], false), ([false], true)]) := by
  unfold observeCache
  rw [BitOraclePrimitiveCanary.run_handler]
  rfl

/-- The same clock works when a cached shorter answer changes the next request. -/
theorem occupied_changes_request :
    observeCache [false] ⟨[([false], ⟨[true], by decide⟩)], []⟩ =
      (some (none, [false], [true], [true, true], [true]),
        [([false], true), ([true], false), ([false], true)]) := by
  unfold observeCache
  rw [BitOraclePrimitiveCanary.run_handler]
  rfl

private def emptyHandler : QueryImpl (spec 0) (StateT Nat Id) := fun request count =>
  match request with
  | .coin => (⟨true, trivial⟩, count + 1)
  | .hash _ => (⟨[], Nat.zero_le _⟩, count + 1)

/-- Zero-width answers still execute all three queries and preserve the entire caller. -/
theorem zero_width :
    let out := (observe <$> simulateQ emptyHandler (simulateQ (adapter 0)
      (BitOraclePrimitiveLoop.run code (BitOraclePrimitiveCanary.clock 0 [false] [true, false])
        (lower code (ready (initial [false]) (wordTape [true, false]) (wordTape [true])))))).run 0
    out.1 = some (final [false] [] [] []) ∧ out.2 = 3 := by
  rw [BitOraclePrimitiveCanary.run_handler]
  exact ⟨rfl, rfl⟩

private def emptyCaller : BitOracleMachine.Config 1 1 1 := ⟨some 0, 0, fun _ => []⟩

private def spinning : BitOracleMachine.Code 1 1 1 := fun _ => .coin 0 0
private def countHandler : QueryImpl BitOracleMachine.spec (StateT Nat Id) := fun q count =>
  match q with
  | .coin => (true, count + 1)
  | .hash _ => ([], count + 1)

/-- Padding a live source boundary makes additional actual primitive-loop queries. -/
theorem live_padding_adds_queries :
    ((simulateQ countHandler (BitOracleMachine.run spinning 1 emptyCaller)).run 0).2 = 1 ∧
    1 < ((simulateQ countHandler (BitOraclePrimitiveLoop.run spinning 2000
      (lower spinning (ready emptyCaller (wordTape []) (wordTape []))))).run 0).2 := by decide +kernel

/-- Finiteness covers arbitrary words and every primitive observation time,
including this nonterminating coin program's intermediate configurations. -/
theorem arbitrary_reachable_control (fuel : Nat) (word : List Bool) :
    ∀ out ∈ support (BitOraclePrimitiveLoop.run spinning fuel
      (lower spinning (ready {emptyCaller with stk := fun _ => word} (wordTape word) (wordTape word)))),
      BitOraclePrimitiveFinite.control out ∈ BitOraclePrimitiveFinite.controlSupport spinning :=
  BitOraclePrimitiveFinite.reachable_control spinning fuel _ _ _

/-- Dropping the live source label would identify different finite controls. -/
theorem control_retains_label :
    BitOraclePrimitiveFinite.control (BitOraclePrimitiveLoop.State.ready (s := 1) (some (0 : Fin 1))
      (0 : Fin 1) ⟨default, default, default⟩) ≠
    BitOraclePrimitiveFinite.control (.ready none (0 : Fin 1) ⟨default, default, default⟩) := by
  intro h
  cases h

/-- Saved local memory is also present in the finite-control projection. -/
theorem control_retains_memory :
    BitOraclePrimitiveFinite.control (BitOraclePrimitiveLoop.State.ready (s := 1) (some (0 : Fin 1))
      (0 : Fin 2) ⟨default, default, default⟩) ≠
    BitOraclePrimitiveFinite.control (.ready (some 0) (1 : Fin 2) ⟨default, default, default⟩) := by
  intro h
  have hm := BitOraclePrimitiveLoop.State.ready.inj h
  have bad := congrArg Fin.val hm.2.1
  contradiction

private def received (word : List Bool) : BitOraclePrimitiveLoop.State 1 1 1 :=
  .input 0 (0, 0) (wordTape []) ⟨.seekWork, default, wordTape word⟩

/-- Arbitrary native answer words live on the answer tape, outside finite
control, and reconstruction still retains the complete original state. -/
theorem native_word_storage (a b : List Bool) :
    BitOraclePrimitiveFinite.control (received a) = BitOraclePrimitiveFinite.control (received b) ∧
    BitOraclePrimitiveFinite.withTapes (BitOraclePrimitiveFinite.tapes (received a))
      (BitOraclePrimitiveFinite.control (received a)) = received a ∧
    OracleTapeDispatch.readWord (BitOraclePrimitiveFinite.tapes (received a)).answer = a := by
  exact ⟨rfl, BitOraclePrimitiveFinite.reconstruct _, OracleTapeDispatch.read_wordTape _⟩

end ExplainableCrypto.Helios.Computational.OraclePrimitiveContractControls
