import ExplainableCrypto.Helios.Computational.ReplayBitsExecution

/-! Literal bit frames, range failures and actual direct-collector controls. -/
namespace ExplainableCrypto.Helios.Computational.ReplayBitsControls
open OracleComp OracleSpec

def hash0 : ReplayEvent 11 := ⟨.inr (),(0 : ZMod 11)⟩
def hash1 : ReplayEvent 11 := ⟨.inr (),(1 : ZMod 11)⟩
def unif0 : ReplayEvent 11 := ⟨.inl 0,(0 : Fin 1)⟩
def oneHashWord : List Bool := [true,false,true,true,true,false,false,true,true,false]

/-- Every modulus itself is rejected, rather than silently decoded as zero. -/
theorem scalar_modulus_rejected (q : Nat) : scalarDecode q (uniformNatEncode q) = none := by
  have h := uniformNatRead_encode q []
  simp only [List.append_nil] at h
  simp [scalarDecode,h]

/-- Literal frames fix event tag, count and encoded payload length. -/
theorem literal_frames : replayTapeEncode ([] : ReplayTape 11) = [false] ∧
    replayTapeEncode [hash0] = oneHashWord ∧
    replayTapeDecode 11 oneHashWord = some [hash0] ∧
    replayEventEncode unif0 = [false,false,false] ∧
    replayEventEncode hash1 = [true,true,false,true] := by decide

/-- Wrong count, incomplete frame, altered event tag and trailing data reject. -/
theorem malformed_frames : replayTapeDecode 11 [false,false] = none ∧
    replayTapeDecode 11 (oneHashWord.take 9) = none ∧
    replayTapeDecode 11
      [true,true,false,false,true,true,true,false,false,true,true,false] = none ∧
    replayTapeDecode 11
      [true,false,true,true,true,false,false,true,false,false] = none := by decide

/-- An empty source writes the canonical empty tape directly. -/
theorem empty_source_bits :
    replayBitsCollect (pure () : OracleComp (FiatShamir.Fork.wrappedSpec (ZMod 11)) Unit) =
      pure [false] := rfl

/-- One actual challenge query writes its answer, including the event tag and
framing, with no additional oracle query and no preliminary typed-tape pass. -/
theorem challenge_source_bits :
    replayBitsCollect (FiatShamir.Fork.wrappedChallengeQuery (ZMod 11)) =
      (do let a ← FiatShamir.Fork.wrappedChallengeQuery (ZMod 11)
          pure (uniformNatEncode 1 ++ replayEventFrame (⟨.inr (),a⟩ : ReplayEvent 11))) := by
  change (PFunctor.FreeM.liftBind (P := (FiatShamir.Fork.wrappedSpec (ZMod 11)).toPFunctor)
    (Sum.inr ()) _) = PFunctor.FreeM.liftBind (Sum.inr ()) _
  congr 1
  funext a
  change PFunctor.FreeM.pure (uniformNatEncode 1 ++ (replayEventFrame ⟨.inr (),a⟩ ++ [])) = _
  rw [List.append_nil]
  rfl

#print axioms scalar_modulus_rejected
#print axioms literal_frames
#print axioms malformed_frames
#print axioms empty_source_bits
#print axioms challenge_source_bits
end ExplainableCrypto.Helios.Computational.ReplayBitsControls
