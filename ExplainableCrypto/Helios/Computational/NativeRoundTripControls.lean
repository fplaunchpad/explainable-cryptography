import ExplainableCrypto.Helios.Computational.NativeRoundTripGate
import ExplainableCrypto.Helios.Computational.NativeReturnObservation

/-! Kernel reductions of independent importer and round-trip fixtures. The
Boolean comparison checks every stack, head/control, exact charged cost, and
all oracle events. Expected words below are literal independent encodings. -/
namespace ExplainableCrypto.Helios.Computational.NativeRoundTripControls
open NativeRoundTripGate
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

private def frame : Fin 3 → List Bool :=
  ![[false,false,true,true],[true,false,true],[false,true]]

theorem empty_reply_replaces_old_storage : same
    (Importer.observe NativeAnswerImport.program [true,false] [] [false,true] frame)
    (Importer.endpoint 0 [] [] [] frame 30) = true := by decide +kernel

theorem false_reply_head : same
    (Importer.observe NativeAnswerImport.program [true] [false] [false] frame)
    (Importer.endpoint 1 [] [] [] frame 33) = true := by decide +kernel

theorem reply_order : same
    (Importer.observe NativeAnswerImport.program [false,true] [true,false,true,false]
      [true,false,true] frame)
    (Importer.endpoint 2 [] [true,false,true,true,true,false] [] frame 69) = true := by decide +kernel

theorem wrong_clear_regression : same
    (Importer.observe Importer.wrongClear [true,false] [false,true,true] [false,true] frame)
    (Importer.endpoint 1 [] [true,true] [] frame 43) = true := by decide +kernel

theorem uncleared_query_regression : same
    (Importer.observe Importer.leaveQuery [true,false] [false,true,true] [false,true] frame)
    (Importer.endpoint 1 [] [true,true,true,true] [false,true] frame 49) = true := by decide +kernel

theorem omitted_head_regression : same
    (Importer.observe Importer.skipHead [true,false] [false,true,true] [false,true] frame)
    (Importer.endpoint 0 [] [true,false,true,true,true,true] [] frame 55) = true := by decide +kernel

namespace Whole
open NativeRoundTripGate.RoundTrip

private def noCells : Fin 3 → List Cell := ![[],[],[]]
private def emptyWords : Fin 10 → List Bool :=
  ![[],[],[],[],[],[],[],[],[true,false],[false,true,true]]

/-- Empty replacement still resumes the continuation selected by the old head. -/
theorem empty_hash_live_return : same
    (observe (NativeRoundTrip.code (native false)) ![none,none,some true]
      noCells noCells [true,false] [false,true,true] [] false)
    (endpoint 2 0 emptyWords 45 [.hash []]) = true := by decide +kernel

/-- A false coin becomes a false answer head; query's false head is retained. -/
theorem false_coin_live_return : same
    (observe (NativeRoundTrip.code (native true)) ![none,some false,some true]
      noCells noCells [true,false] [false,true,true] [] false)
    (endpoint 2 12 emptyWords 70 [.coin]) = true := by decide +kernel

/-- Nonempty old answer halves disappear, but every other encoded cell remains,
including a query suffix after the first blank and arbitrary private bits. -/
theorem literal_hash_roundtrip : same
    (observe (NativeRoundTrip.code (native true)) fixtureHeads fixtureBefore fixtureAfter
      [false,true,false] [true,false,true,true] [false,true,true] false)
    (endpoint 2 39 fixtureWords 125 [.hash [false,true]]) = true := by decide +kernel

theorem wrong_live_return_regression : same
    (observe (wrongReturn (NativeRoundTrip.code (native true)))
      fixtureHeads fixtureBefore fixtureAfter
      [false,true,false] [true,false,true,true] [false,true,true] false)
    (endpoint 1 39 fixtureWords 125 [.hash [false,true]]) = true := by decide +kernel

theorem work_corruption_regression : same
    (observe (corruptStorage 0 (NativeRoundTrip.code (native true)))
      fixtureHeads fixtureBefore fixtureAfter
      [false,true,false] [true,false,true,true] [false,true,true] false)
    (endpoint 2 39 (Function.update fixtureWords (0 : Fin 10) [true,false,false,true,true])
      126 [.hash [false,true]]) = true := by decide +kernel

/-- Writing the reply to the before half leaves old encoded cells to be read
as the new raw reply, a different physical state despite a successful return. -/
theorem answer_replacement_regression : same
    (observe (wrongAnswerPort (NativeRoundTrip.code (native true)))
      ![some false,some false,some true] ![[],[],[some false]] ![[],[],[none]]
      [true,false] [false,true,true] [true] false)
    (endpoint 2 39
      ![[],[],[],[],[],[true,false],[],[],[true,false],[false,true,true]]
      85 [.hash [false]]) = true := by decide +kernel

theorem leftover_scratch_regression : same
    (observe (corruptStorage 7 (NativeRoundTrip.code (native true)))
      fixtureHeads fixtureBefore fixtureAfter
      [false,true,false] [true,false,true,true] [false,true,true] false)
    (endpoint 2 39 (Function.update fixtureWords (7 : Fin 10) [true])
      126 [.hash [false,true]]) = true := by decide +kernel

end Whole

private theorem gate_native_boundary (label : Fin 81) :
    decide (label.val < 3) = NativeRoundTrip.atNative (l := 3) label := by
  fin_cases label <;> rfl

/-- The campaign's private observer equals the public observer on every state,
including halted states and arbitrary code, with exactly the same total charge. -/
theorem gate_observer_eq (p : BitOracleMachine.Code 10 81 81) (fuel : Nat)
    (cfg : NativeRoundTripGate.RoundTrip.State) :
    NativeRoundTripGate.RoundTrip.toReturn p fuel cfg =
      NativeReturnObservation.run (@NativeRoundTrip.atNative 3) p fuel cfg := by
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih =>
    rcases cfg with ⟨label,v,words⟩
    cases label with
    | none =>
      simp [NativeRoundTripGate.RoundTrip.toReturn,NativeReturnObservation.run,
        NativeReturnObservation.stopped,BitOracleMachine.step,ih]
      exact NativeReturnObservation.stopped_run _ p fuel _ rfl
    | some label =>
      simp only [NativeRoundTripGate.RoundTrip.toReturn,NativeReturnObservation.run,
        NativeReturnObservation.stopped,Option.any_some,Option.elim_some,gate_native_boundary,ih]
      rfl


end ExplainableCrypto.Helios.Computational.NativeRoundTripControls
