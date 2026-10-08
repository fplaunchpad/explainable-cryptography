import ExplainableCrypto.Helios.Computational.PublicObservationCodec
import ExplainableCrypto.Helios.Computational.BallotOutputBitSize
import ExplainableCrypto.Helios.Computational.BallotCacheCodecControls

/-! Output-field and representation/cryptographic-rejection controls. The
literal public view is a data fixture, not an asserted honest execution. -/
namespace ExplainableCrypto.Helios.Computational.BallotOutputCodecControls
open BallotCacheCodecControls

def badProof : Proof01 (ZMod 11) (PrimeGroup 23 11) := ⟨⟨0,0,0,1⟩,⟨0,0,0,0⟩⟩
def badBallot : Ballot (ZMod 11) (PrimeGroup 23 11) 2 := ⟨fun _ => (0,0),fun _ => badProof,badProof⟩
def before : PublicPrefix (ZMod 11) (PrimeGroup 23 11) :=
  ⟨⟨key.1.publicKey,key.2.1.2,⟨0,1⟩,[0,1],[0,1,2]⟩,21,
    (.accepted,.invalidProof),[⟨0,badBallot⟩]⟩
def view : PublicResult (ZMod 11) (PrimeGroup 23 11) :=
  ⟨before,badBallot,.reusedCiphertext,[⟨0,badBallot⟩],fun _ => (0,0),fun _ => 0,
    fun _ => ⟨(0,0),1⟩,![none,some 0]⟩

theorem representation_not_validity :
    (ballotBitCodec 23 11).decode ((ballotBitCodec 23 11).encode badBallot) = some badBallot ∧
    repairedSubmit (fun _ _ _ _ => (0 : ZMod 11)) key.1.publicKey key.2.1.2 2
      [⟨0,badBallot⟩] badBallot = (.invalidProof,[⟨0,badBallot⟩]) :=
  by
    refine ⟨ballotBits_roundTrip _,?_⟩
    have hv : ¬badBallot.StrongValid (fun _ _ _ _ => (0 : ZMod 11)) key.1.publicKey key.2.1.2 := by decide
    simp [repairedSubmit,hv]

theorem aggregate_response_retained :
    (ballotBitCodec 23 11).encode badBallot ≠
      (ballotBitCodec 23 11).encode
        {badBallot with overall := {badProof with zero := {badProof.zero with response := 2}}} := by
  intro h
  have he := congrArg (fun b => b.overall.zero.response) (BitRecordCodec.injective _ h)
  exact (by decide : (1 : ZMod 11) ≠ 2) he

theorem voter_identity_retained :
    (ballotBoardBitCodec 23 11).encode [⟨0,badBallot⟩] ≠
      (ballotBoardBitCodec 23 11).encode [⟨1,badBallot⟩] := by
  intro h
  have he := congrArg (fun b => b.map BoardEntry.voter) (BitRecordCodec.injective _ h)
  exact (by decide : [0] ≠ ([1] : List (Fin 3))) he

theorem decision_tags : ballotDecisionBitCodec.encode .accepted = [false,false] ∧
    ballotDecisionBitCodec.encode .invalidProof = [false,true] ∧
    ballotDecisionBitCodec.encode .reusedCiphertext = [true,false] ∧
    ballotDecisionBitCodec.decode [true,true] = none := by decide

theorem decoding_failure_distinct : ballotDecodedBitCodec.encode none = [false] ∧
    ballotDecodedBitCodec.encode (some 0) = [true,false] ∧
    ballotDecodedBitCodec.decode [false,false] = none := by decide

theorem fingerprint_retained :
    (ballotPublicResultBitCodec 23 11).encode view ≠
      (ballotPublicResultBitCodec 23 11).encode {view with beforeTally := {before with fingerprint := 22}} := by
  intro h
  have he := congrArg (fun r => r.beforeTally.fingerprint) (ballotPublicResultBits_injective h)
  exact (by decide : (21 : Nat) ≠ 22) he

theorem trustee_proof_retained :
    (ballotPublicResultBitCodec 23 11).encode view ≠
      (ballotPublicResultBitCodec 23 11).encode
        {view with decryptionProofs := fun _ => ⟨(0,0),2⟩} := by
  intro h
  have he := congrArg (fun r => (r.decryptionProofs 0).response) (ballotPublicResultBits_injective h)
  exact (by decide : (1 : ZMod 11) ≠ 2) he

theorem decoded_tally_retained :
    (ballotPublicResultBitCodec 23 11).encode view ≠
      (ballotPublicResultBitCodec 23 11).encode {view with decodedTally := fun _ => some 0} := by
  intro h
  have he := congrArg (fun r => r.decodedTally 0) (ballotPublicResultBits_injective h)
  cases he

#print axioms representation_not_validity
#print axioms aggregate_response_retained
#print axioms voter_identity_retained
#print axioms decision_tags
#print axioms decoding_failure_distinct
#print axioms fingerprint_retained
#print axioms trustee_proof_retained
#print axioms decoded_tally_retained
end ExplainableCrypto.Helios.Computational.BallotOutputCodecControls
