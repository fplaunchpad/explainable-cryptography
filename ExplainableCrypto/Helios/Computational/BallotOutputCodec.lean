import ExplainableCrypto.Helios.Computational.BallotStateCodec
import ExplainableCrypto.Helios.Computational.RepairedSubmissionOracle
import Mathlib.Logic.Equiv.Fin.Basic

/-! Complete ballot/submission records. Decoding checks representation, not
cryptographic validity; the original verifier still determines rejection. -/
namespace ExplainableCrypto.Helios.Computational

/-- Fixed arity uses Mathlib's computable two-function/product equivalence. -/
def ballotTwoBitCodec {A : Type} (c : BitRecordCodec A) : BitRecordCodec (Fin 2 → A) :=
  (c.pair c).equiv (finTwoArrowEquiv A).symm

def ballotVoterBitCodec : BitRecordCodec (Fin 3) :=
  (primeScalarBitCodec 3).equiv (ZMod.finEquiv 3).toEquiv.symm

/-- Three distinct decision tags; the unused tag and wrong lengths reject. -/
def ballotDecisionBitCodec : BitRecordCodec Decision where
  encode d := match d with
    | .accepted => [false,false]
    | .invalidProof => [false,true]
    | .reusedCiphertext => [true,false]
  decode w := match w with
    | [false,false] => some .accepted
    | [false,true] => some .invalidProof
    | [true,false] => some .reusedCiphertext
    | _ => none
  roundTrip d := by cases d <;> rfl
  exact w d h := by
    split at h <;> first | (cases Option.some.inj h; rfl) | cases h

variable (p q : Nat) [NeZero p] [NeZero q]

def ballotCiphertextBitCodec : BitRecordCodec (Ciphertext (PrimeGroup p q)) :=
  (primeGroupBitCodec p q).pair (primeGroupBitCodec p q)

def ballotBranchBitCodec : BitRecordCodec (Branch (ZMod q) (PrimeGroup p q)) :=
  ((ballotCiphertextBitCodec p q).pair
    ((primeScalarBitCodec q).pair (primeScalarBitCodec q))).equiv
    { toFun := fun x => ⟨x.1.1,x.1.2,x.2.1,x.2.2⟩
      invFun := fun b => ((b.a,b.b),b.challenge,b.response)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def ballotProofBitCodec : BitRecordCodec (Proof01 (ZMod q) (PrimeGroup p q)) :=
  ((ballotBranchBitCodec p q).pair (ballotBranchBitCodec p q)).equiv
    { toFun := fun x => ⟨x.1,x.2⟩
      invFun := fun b => (b.zero,b.one)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def ballotBitCodec : BitRecordCodec (Ballot (ZMod q) (PrimeGroup p q) 2) :=
  ((ballotTwoBitCodec (ballotCiphertextBitCodec p q)).pair
    ((ballotTwoBitCodec (ballotProofBitCodec p q)).pair (ballotProofBitCodec p q))).equiv
    { toFun := fun x => ⟨x.1,x.2.1,x.2.2⟩
      invFun := fun b => (b.ciphertext,b.proof,b.overall)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def ballotBoardEntryBitCodec : BitRecordCodec (BoardEntry (ZMod q) (PrimeGroup p q)) :=
  (ballotVoterBitCodec.pair (ballotBitCodec p q)).equiv
    { toFun := fun x => ⟨x.1,x.2⟩
      invFun := fun e => (e.voter,e.ballot)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def ballotBoardBitCodec : BitRecordCodec (List (BoardEntry (ZMod q) (PrimeGroup p q))) :=
  (ballotBoardEntryBitCodec p q).list

def ballotHonestViewBitCodec : BitRecordCodec (HonestPrefixView (ZMod q) (PrimeGroup p q)) :=
  (ballotDecisionBitCodec.pair ballotDecisionBitCodec).pair (ballotBoardBitCodec p q)

def ballotSubmissionBitCodec : BitRecordCodec (RepairedSubmissionResult (ZMod q) (PrimeGroup p q)) :=
  ((ballotHonestViewBitCodec p q).pair ((ballotBitCodec p q).pair
    (ballotDecisionBitCodec.pair (ballotBoardBitCodec p q)))).equiv
    { toFun := fun x => ⟨x.1,x.2.1,x.2.2.1,x.2.2.2⟩
      invFun := fun r => (r.honest,r.ballot,r.decision,r.board)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

variable {p q}

theorem ballotProofBits_roundTrip (b : Proof01 (ZMod q) (PrimeGroup p q)) :
    (ballotProofBitCodec p q).decode ((ballotProofBitCodec p q).encode b) = some b :=
  BitRecordCodec.roundTrip _ _

theorem ballotBits_roundTrip (b : Ballot (ZMod q) (PrimeGroup p q) 2) :
    (ballotBitCodec p q).decode ((ballotBitCodec p q).encode b) = some b :=
  BitRecordCodec.roundTrip _ _

theorem ballotBits_exact (w : List Bool) (b : Ballot (ZMod q) (PrimeGroup p q) 2)
    (h : (ballotBitCodec p q).decode w = some b) : w = (ballotBitCodec p q).encode b :=
  BitRecordCodec.exact _ _ _ h

theorem ballotBoardBits_roundTrip (b : List (BoardEntry (ZMod q) (PrimeGroup p q))) :
    (ballotBoardBitCodec p q).decode ((ballotBoardBitCodec p q).encode b) = some b :=
  BitRecordCodec.roundTrip _ _

theorem ballotBoardBits_exact (w : List Bool) (b : List (BoardEntry (ZMod q) (PrimeGroup p q)))
    (h : (ballotBoardBitCodec p q).decode w = some b) : w = (ballotBoardBitCodec p q).encode b :=
  BitRecordCodec.exact _ _ _ h

theorem ballotSubmissionBits_roundTrip (r : RepairedSubmissionResult (ZMod q) (PrimeGroup p q)) :
    (ballotSubmissionBitCodec p q).decode ((ballotSubmissionBitCodec p q).encode r) = some r :=
  BitRecordCodec.roundTrip _ _

theorem ballotSubmissionBits_exact (w : List Bool)
    (r : RepairedSubmissionResult (ZMod q) (PrimeGroup p q))
    (h : (ballotSubmissionBitCodec p q).decode w = some r) :
    w = (ballotSubmissionBitCodec p q).encode r := BitRecordCodec.exact _ _ _ h

open OracleComp OracleSpec

/-- Decode submission inputs, run the original shared-oracle verifier and
encode its decision/board. Malformed records remain separate from rejection. -/
def repairedSubmitBitsOracle (p q : Nat) [NeZero p] [Fact q.Prime]
    (g pk : PrimeGroup p q) (voterWord boardWord ballotWord : List Bool) :
    BallotOracleComp (ZMod q) (PrimeGroup p q) (Option (List Bool)) :=
  match ballotVoterBitCodec.decode voterWord,
    (ballotBoardBitCodec p q).decode boardWord,(ballotBitCodec p q).decode ballotWord with
  | some voter,some board,some ballot =>
    (fun out => some ((ballotDecisionBitCodec.pair (ballotBoardBitCodec p q)).encode out)) <$>
      repairedSubmitOracle g pk voter board ballot
  | _,_,_ => pure none

theorem repairedSubmitBitsOracle_encode {p q : Nat} [NeZero p] [Fact q.Prime]
    (g pk : PrimeGroup p q) (voter : Fin 3)
    (board : List (BoardEntry (ZMod q) (PrimeGroup p q))) (b : Ballot (ZMod q) (PrimeGroup p q) 2) :
    repairedSubmitBitsOracle p q g pk (ballotVoterBitCodec.encode voter)
      ((ballotBoardBitCodec p q).encode board) ((ballotBitCodec p q).encode b) =
      (fun out => some ((ballotDecisionBitCodec.pair (ballotBoardBitCodec p q)).encode out)) <$>
        repairedSubmitOracle g pk voter board b := by
  simp [repairedSubmitBitsOracle,BitRecordCodec.roundTrip]

#print axioms ballotProofBits_roundTrip
#print axioms ballotBits_roundTrip
#print axioms ballotBits_exact
#print axioms ballotBoardBits_roundTrip
#print axioms ballotBoardBits_exact
#print axioms ballotSubmissionBits_roundTrip
#print axioms ballotSubmissionBits_exact
#print axioms repairedSubmitBitsOracle_encode
end ExplainableCrypto.Helios.Computational
