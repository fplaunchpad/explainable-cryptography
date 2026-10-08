import ExplainableCrypto.Helios.Computational.UniformOperandCodec
import ExplainableCrypto.Helios.Computational.BallotTapeOperandControls

/-! Independent bit fixtures and supported wide-uniform operands. -/
namespace ExplainableCrypto.Helios.Computational.UniformOperandCodecControls
open OracleComp OracleSpec BallotTapeOperandControls

def zero : UniformEvent := ⟨0,0⟩
def coin0 : UniformEvent := ⟨1,0⟩
def coin1 : UniformEvent := ⟨1,1⟩

/-- Independent literal encodings pin width framing and the order of operands. -/
theorem literal_events : uniformEventEncode zero = [false,false] ∧
    uniformEventEncode coin0 = [true,false,true,false] ∧
    uniformEventEncode coin1 = [true,false,true,true,false,true] ∧
    uniformEventDecode [true,false,true,false] = some coin0 ∧
    uniformEventDecode [true,false,true,true,false,true] = some coin1 := by decide

/-- Truncated prefixes/payloads, padded zero, an answer outside its declared range
and an ignored trailing bit all reject for the actual event decoder. -/
theorem malformed_events : uniformEventDecode [] = none ∧
    uniformEventDecode [true] = none ∧ uniformEventDecode [true,false] = none ∧
    uniformEventDecode [true,false,false,false] = none ∧
    uniformEventDecode [false,true,false,true] = none ∧
    uniformEventDecode [false,false,true] = none := by decide

/-- Reading a natural leaves the exact next-operand bits untouched. -/
theorem prefix_fixture : uniformNatEncode 2 = [true,true,false,false,true] ∧
    uniformNatRead [true,true,false,false,true,false,true] = some (2,[false,true]) := by decide

/-- Apply the codec to the event of the checked supported one-query tape family.
It has 2k+4 encoded bits; no bound independent of operand width is introduced. -/
theorem supported_wide_event (k : Nat) :
    zeroTape k ∈ support (ballotReplayCollectTape (wideQuery k)) ∧
    (uniformEventEncode (⟨2^k,0⟩ : UniformEvent)).length = 2*k+4 ∧
    uniformEventDecode (uniformEventEncode (⟨2^k,0⟩ : UniformEvent)) = some ⟨2^k,0⟩ := by
  refine ⟨(wide_tape k).2.1,?_,uniformEventDecode_encode _⟩
  rw [uniformEventEncode_length]
  simp only [Nat.size_pow,Fin.val_zero,Nat.size_zero]
  omega

#print axioms literal_events
#print axioms malformed_events
#print axioms prefix_fixture
#print axioms supported_wide_event
end ExplainableCrypto.Helios.Computational.UniformOperandCodecControls
