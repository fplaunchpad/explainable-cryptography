import ExplainableCrypto.Helios.Computational.BallotStateBitSize
import ExplainableCrypto.Helios.Computational.BallotCacheCodecControls

/-! Independent collision, sticky flag, history-order and distinct-cache controls. -/
namespace ExplainableCrypto.Helios.Computational.BallotStateCodecControls
open BallotCacheCodecControls

def state : BallotFiniteProgrammedState (ZMod 11) (PrimeGroup 23 11) :=
  ⟨cache,false,[otherKey.1,key.1]⟩

def transcript : BallotCommitment (PrimeGroup 23 11) × ZMod 11 × BallotResponse (ZMod 11) :=
  (key.2,7,1,2,3)

theorem occupied_transition :
    (state.program key.1 transcript).2.bad = true ∧
    (state.program key.1 transcript).2.cache.lookup key = some 3 ∧
    (state.program key.1 transcript).2.programmed = [key.1,otherKey.1,key.1] := by decide

/-- Execute the encoded transition and decode its result; the occupied key
keeps answer three rather than the sampled seven, with flag and repeated history. -/
theorem encoded_occupied_transition :
    ((ballotProgrammedBitsApply 23 11 ((ballotProgrammedBitCodec 23 11).encode state)
      key.1 transcript).bind (fun out => (ballotProgrammedBitCodec 23 11).decode out.2)).map
        (fun s => (s.bad,s.cache.lookup key,s.programmed)) =
      some (true,some 3,[key.1,otherKey.1,key.1]) := by
  rw [ballotProgrammedBitsApply_encode]
  dsimp only [Option.bind]
  rw [BitRecordCodec.roundTrip]
  change some ((state.program key.1 transcript).2.bad,
    (state.program key.1 transcript).2.cache.lookup key,
    (state.program key.1 transcript).2.programmed) = _
  rw [occupied_transition.1,occupied_transition.2.1,occupied_transition.2.2]

/-- Repeated requests are retained even when they carry the same statement. -/
theorem history_not_deduplicated :
    (ballotProgrammedBitCodec 23 11).encode ⟨cache,true,[key.1,key.1]⟩ ≠
      (ballotProgrammedBitCodec 23 11).encode ⟨cache,true,[key.1]⟩ := by
  intro h
  have he := BitRecordCodec.injective _ h
  have hl := congrArg (fun s => s.programmed.length) he
  exact (by decide : (2 : Nat) ≠ 1) hl

theorem flag_not_erased :
    (ballotProgrammedBitCodec 23 11).encode ⟨cache,true,[]⟩ ≠
      (ballotProgrammedBitCodec 23 11).encode ⟨cache,false,[]⟩ := by
  intro h
  have he := congrArg BallotFiniteProgrammedState.bad (BitRecordCodec.injective _ h)
  cases he

theorem live_cache_not_erased :
    (ballotBothCachesBitCodec 23 11).encode (state,cache) ≠
      (ballotBothCachesBitCodec 23 11).encode (state,∅) := by
  intro h
  have he := congrArg (fun s => s.2.entries.length) (BitRecordCodec.injective _ h)
  exact (by decide : cache.entries.length ≠ 0) he

theorem chronological_log_not_reversed :
    (ballotLoggedBitCodec 23 11).encode (cache,[((),key),((),otherKey)]) ≠
      (ballotLoggedBitCodec 23 11).encode (cache,[((),otherKey),((),key)]) := by
  intro h
  have he := congrArg Prod.snd (BitRecordCodec.injective _ h)
  exact (by decide : [((),key),((),otherKey)] ≠ [((),otherKey),((),key)]) he

theorem malformed_flag : ballotBoolBitCodec.decode [false,true] = none ∧
    ballotBoolBitCodec.decode [] = none := by decide

#print axioms occupied_transition
#print axioms encoded_occupied_transition
#print axioms history_not_deduplicated
#print axioms flag_not_erased
#print axioms live_cache_not_erased
#print axioms chronological_log_not_reversed
#print axioms malformed_flag
end ExplainableCrypto.Helios.Computational.BallotStateCodecControls
