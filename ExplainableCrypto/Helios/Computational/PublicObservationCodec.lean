import ExplainableCrypto.Helios.Computational.BallotOutputCodec
import ExplainableCrypto.Helios.Computational.RepairedExecution

/-! All fields of the existing public election views, including trustee proofs,
fingerprint and decoding failures. This is not a new election input policy. -/
namespace ExplainableCrypto.Helios.Computational

def ballotNatBitCodec : BitRecordCodec Nat where
  encode := uniformNatEncode
  decode word := do
    let (n,suffix) ← uniformNatRead word
    if suffix = [] then some n else none
  roundTrip n := by
    have hr := uniformNatRead_encode n []
    simp only [List.append_nil] at hr
    simp [hr]
  exact word n h := by
    cases hr : uniformNatRead word with
    | none => simp [hr] at h
    | some pair =>
      rcases pair with ⟨value,suffix⟩
      simp only [hr] at h
      dsimp only [Bind.bind,Option.bind] at h
      split at h
      · rename_i hs
        subst suffix
        cases Option.some.inj h
        simpa only [List.append_nil] using uniformNatRead_exact word _ [] hr
      · cases h

/-- A missing decoded tally is distinct from decoded zero. -/
def ballotDecodedBitCodec : BitRecordCodec (Option Nat) where
  encode value := match value with | none => [false] | some n => true::ballotNatBitCodec.encode n
  decode word := match word with
    | [false] => some none
    | true::rest => (ballotNatBitCodec.decode rest).map some
    | _ => none
  roundTrip value := by cases value <;> simp [BitRecordCodec.roundTrip]
  exact word value h := by
    split at h
    · cases Option.some.inj h; rfl
    · rename_i rest
      obtain ⟨n,hn,he⟩ := Option.map_eq_some_iff.mp h
      subst value
      rw [BitRecordCodec.exact _ rest n hn]
    · cases h

variable (p q : Nat) [NeZero p] [NeZero q]

def ballotSchnorrBitCodec {A : Type} (c : BitRecordCodec A) : BitRecordCodec (SchnorrProof (ZMod q) A) :=
  (c.pair (primeScalarBitCodec q)).equiv
    { toFun := fun x => ⟨x.1,x.2⟩
      invFun := fun pr => (pr.commitment,pr.response)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def ballotParametersBitCodec : BitRecordCodec (PublicParameters (ZMod q) (PrimeGroup p q)) :=
  ((ballotCiphertextBitCodec p q).pair
    ((ballotSchnorrBitCodec q (primeGroupBitCodec p q)).pair
      (ballotNatBitCodec.list.pair ballotVoterBitCodec.list))).equiv
    { toFun := fun x => ⟨x.1.1,x.1.2,x.2.1,x.2.2.1,x.2.2.2⟩
      invFun := fun r => ((r.generator,r.publicKey),r.trusteeKeyProof,r.candidates,r.eligibleVoters)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def ballotPublicPrefixBitCodec : BitRecordCodec (PublicPrefix (ZMod q) (PrimeGroup p q)) :=
  ((ballotParametersBitCodec p q).pair (ballotNatBitCodec.pair (ballotHonestViewBitCodec p q))).equiv
    { toFun := fun x => ⟨x.1,x.2.1,x.2.2.1,x.2.2.2⟩
      invFun := fun r => (r.parameters,r.fingerprint,r.honestDecisions,r.board)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def ballotPublicResultBitCodec : BitRecordCodec (PublicResult (ZMod q) (PrimeGroup p q)) :=
  ((ballotPublicPrefixBitCodec p q).pair ((ballotBitCodec p q).pair
    (ballotDecisionBitCodec.pair ((ballotBoardBitCodec p q).pair
      ((ballotTwoBitCodec (ballotCiphertextBitCodec p q)).pair
        ((ballotTwoBitCodec (primeGroupBitCodec p q)).pair
          ((ballotTwoBitCodec (ballotSchnorrBitCodec q (ballotCiphertextBitCodec p q))).pair
            (ballotTwoBitCodec ballotDecodedBitCodec)))))))).equiv
    { toFun := fun ⟨before,submission,decision,board,encrypted,shares,proofs,decoded⟩ =>
        ⟨before,submission,decision,board,encrypted,shares,proofs,decoded⟩
      invFun := fun r => (r.beforeTally,r.submission,r.decision,r.board,r.encryptedTally,
        r.decryptionShares,r.decryptionProofs,r.decodedTally)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

variable {p q}

theorem ballotPublicPrefixBits_roundTrip (r : PublicPrefix (ZMod q) (PrimeGroup p q)) :
    (ballotPublicPrefixBitCodec p q).decode ((ballotPublicPrefixBitCodec p q).encode r) = some r :=
  BitRecordCodec.roundTrip _ _

theorem ballotPublicPrefixBits_exact (w : List Bool) (r : PublicPrefix (ZMod q) (PrimeGroup p q))
    (h : (ballotPublicPrefixBitCodec p q).decode w = some r) :
    w = (ballotPublicPrefixBitCodec p q).encode r := BitRecordCodec.exact _ _ _ h

theorem ballotPublicResultBits_roundTrip (r : PublicResult (ZMod q) (PrimeGroup p q)) :
    (ballotPublicResultBitCodec p q).decode ((ballotPublicResultBitCodec p q).encode r) = some r :=
  BitRecordCodec.roundTrip _ _

theorem ballotPublicResultBits_exact (w : List Bool) (r : PublicResult (ZMod q) (PrimeGroup p q))
    (h : (ballotPublicResultBitCodec p q).decode w = some r) :
    w = (ballotPublicResultBitCodec p q).encode r := BitRecordCodec.exact _ _ _ h

theorem ballotPublicResultBits_injective :
    Function.Injective (ballotPublicResultBitCodec p q).encode := BitRecordCodec.injective _

/-- The original complete finishing algorithm behind an internal bit interface.
Hashes and private inputs are still those of the existing typed election game. -/
def finishRepairedElectionBits (p q : Nat) [NeZero p] [Fact q.Prime]
    (hashes : StrongCryptoHashes (ZMod q) (PrimeGroup p q))
    (secret : ZMod q) (nonces : Fin 2 → ZMod q) (prefixWord submissionWord : List Bool) :
    Option (List Bool) := do
  let before ← (ballotPublicPrefixBitCodec p q).decode prefixWord
  let submission ← (ballotBitCodec p q).decode submissionWord
  some ((ballotPublicResultBitCodec p q).encode
    (finishRepairedElection hashes secret nonces before submission))

theorem finishRepairedElectionBits_encode {p q : Nat} [NeZero p] [Fact q.Prime]
    (hashes : StrongCryptoHashes (ZMod q) (PrimeGroup p q))
    (secret : ZMod q) (nonces : Fin 2 → ZMod q)
    (before : PublicPrefix (ZMod q) (PrimeGroup p q))
    (submission : Ballot (ZMod q) (PrimeGroup p q) 2) :
    finishRepairedElectionBits p q hashes secret nonces
      ((ballotPublicPrefixBitCodec p q).encode before) ((ballotBitCodec p q).encode submission) =
      some ((ballotPublicResultBitCodec p q).encode
        (finishRepairedElection hashes secret nonces before submission)) := by
  simp [finishRepairedElectionBits,BitRecordCodec.roundTrip]

#print axioms ballotPublicPrefixBits_roundTrip
#print axioms ballotPublicPrefixBits_exact
#print axioms ballotPublicResultBits_roundTrip
#print axioms ballotPublicResultBits_exact
#print axioms ballotPublicResultBits_injective
#print axioms finishRepairedElectionBits_encode
end ExplainableCrypto.Helios.Computational
