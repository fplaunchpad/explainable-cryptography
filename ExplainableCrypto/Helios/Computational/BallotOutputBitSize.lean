import ExplainableCrypto.Helios.Computational.BallotOutputCodec
import ExplainableCrypto.Helios.Computational.BallotStateBitSize
import ExplainableCrypto.Helios.Computational.RepairedOutputStorage

/-! Complete ballot/submission bit lengths, retaining proof fields, decisions
and voter identifiers. Actual runtime supplies both board counts. -/
namespace ExplainableCrypto.Helios.Computational

def ciphertextRecordBitBound (p : Nat) := bitPairSize (groupRecordBitBound p) (groupRecordBitBound p)
def branchRecordBitBound (p q : Nat) :=
  bitPairSize (ciphertextRecordBitBound p) (bitPairSize (groupRecordBitBound q) (groupRecordBitBound q))
def proofRecordBitBound (p q : Nat) := bitPairSize (branchRecordBitBound p q) (branchRecordBitBound p q)
def ballotRecordBitBound (p q : Nat) :=
  bitPairSize (bitPairSize (ciphertextRecordBitBound p) (ciphertextRecordBitBound p))
    (bitPairSize (bitPairSize (proofRecordBitBound p q) (proofRecordBitBound p q)) (proofRecordBitBound p q))
def boardRecordBitBound (p q n : Nat) := bitListSize (bitPairSize 5 (ballotRecordBitBound p q)) n
def honestViewRecordBitBound (p q n : Nat) := bitPairSize (bitPairSize 2 2) (boardRecordBitBound p q n)
def submissionRecordBitBound (p q n k : Nat) :=
  bitPairSize (honestViewRecordBitBound p q n)
    (bitPairSize (ballotRecordBitBound p q) (bitPairSize 2 (boardRecordBitBound p q k)))

private theorem two_length {A : Type} (c : BitRecordCodec A) (f : Fin 2 → A) (n : Nat)
    (h : ∀ i, (c.encode (f i)).length ≤ n) :
    ((ballotTwoBitCodec c).encode f).length ≤ bitPairSize n n :=
  BitRecordCodec.pair_length_le c c (f 0) (f 1) n n (h 0) (h 1)

private theorem voter_length (v : Fin 3) : (ballotVoterBitCodec.encode v).length ≤ 5 := by
  fin_cases v <;> decide

private theorem decision_length (d : Decision) : (ballotDecisionBitCodec.encode d).length ≤ 2 := by
  cases d <;> rfl

variable {p q : Nat} [NeZero p] [NeZero q]

private theorem cipher_length (ct : Ciphertext (PrimeGroup p q)) :
    ((ballotCiphertextBitCodec p q).encode ct).length ≤ ciphertextRecordBitBound p :=
  BitRecordCodec.pair_length_le _ _ ct.1 ct.2 _ _ (primeGroupEncode_length_le _) (primeGroupEncode_length_le _)

private theorem branch_length (b : Branch (ZMod q) (PrimeGroup p q)) :
    ((ballotBranchBitCodec p q).encode b).length ≤ branchRecordBitBound p q :=
  BitRecordCodec.pair_length_le _ _ (b.a,b.b) (b.challenge,b.response) _ _ (cipher_length _)
    (BitRecordCodec.pair_length_le _ _ b.challenge b.response _ _
      (scalarEncode_length_le _) (scalarEncode_length_le _))

theorem ballotProofBits_length_le (pr : Proof01 (ZMod q) (PrimeGroup p q)) :
    ((ballotProofBitCodec p q).encode pr).length ≤ proofRecordBitBound p q :=
  BitRecordCodec.pair_length_le _ _ pr.zero pr.one _ _ (branch_length _) (branch_length _)

theorem ballotBits_length_le (b : Ballot (ZMod q) (PrimeGroup p q) 2) :
    ((ballotBitCodec p q).encode b).length ≤ ballotRecordBitBound p q :=
  BitRecordCodec.pair_length_le _ _ b.ciphertext (b.proof,b.overall) _ _
    (two_length _ b.ciphertext _ (fun _ => cipher_length _))
    (BitRecordCodec.pair_length_le _ _ b.proof b.overall _ _
      (two_length _ b.proof _ (fun _ => ballotProofBits_length_le _)) (ballotProofBits_length_le _))

theorem ballotBoardBits_length_le (board : List (BoardEntry (ZMod q) (PrimeGroup p q)))
    (n : Nat) (hn : board.length ≤ n) :
    ((ballotBoardBitCodec p q).encode board).length ≤ boardRecordBitBound p q n :=
  BitRecordCodec.list_length_le _ board _ n (fun e _ =>
    BitRecordCodec.pair_length_le _ _ e.voter e.ballot _ _ (voter_length _) (ballotBits_length_le _)) hn

theorem ballotSubmissionBits_length_le (r : RepairedSubmissionResult (ZMod q) (PrimeGroup p q))
    (n k : Nat) (hn : r.honest.2.length ≤ n) (hk : r.board.length ≤ k) :
    ((ballotSubmissionBitCodec p q).encode r).length ≤ submissionRecordBitBound p q n k := by
  have hh : ((ballotHonestViewBitCodec p q).encode r.honest).length ≤ honestViewRecordBitBound p q n :=
    BitRecordCodec.pair_length_le _ _ r.honest.1 r.honest.2 _ _
      (BitRecordCodec.pair_length_le _ _ r.honest.1.1 r.honest.1.2 _ _ (decision_length _) (decision_length _))
      (ballotBoardBits_length_le _ n hn)
  exact BitRecordCodec.pair_length_le _ _ r.honest (r.ballot,r.decision,r.board) _ _ hh
    (BitRecordCodec.pair_length_le _ _ r.ballot (r.decision,r.board) _ _ (ballotBits_length_le _)
      (BitRecordCodec.pair_length_le _ _ r.decision r.board _ _ (decision_length _) (ballotBoardBits_length_le _ k hk)))

open OracleComp OracleSpec

/-- Complete explicit-nonce runtime supplies its prefix/final board counts.
Only runtime support is transported; no replay-path matching is inferred. -/
theorem repairedSubmissionPrime_output_bits_le {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) (PrimeGroup p q) →
      BallotOracleComp (ZMod q) (PrimeGroup p q) (Ballot (ZMod q) (PrimeGroup p q) 2))
    (out : (RepairedSubmissionResult (ZMod q) (PrimeGroup p q) ×
      BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q)) ×
      BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (ho : out ∈ support (runBallotFiniteProgrammed g pk (repairedSubmissionPrimeOracle g pk vote attacker))) :
    ((ballotSubmissionBitCodec p q).encode out.1.1).length ≤ submissionRecordBitBound p q 2 3 := by
  have hold := (mem_support_iff_of_evalSPMF_eq (repairedSubmissionPrime_runtime g pk vote attacker) out).mp ho
  have hs := repairedSubmissionFinite_output_board_lengths g pk vote attacker out hold
  exact ballotSubmissionBits_length_le out.1.1 2 3 hs.1 hs.2

#print axioms ballotProofBits_length_le
#print axioms ballotBits_length_le
#print axioms ballotBoardBits_length_le
#print axioms ballotSubmissionBits_length_le
#print axioms repairedSubmissionPrime_output_bits_le
end ExplainableCrypto.Helios.Computational
