import ExplainableCrypto.Helios.Computational.BallotOutputBitSize

/-! The actual complete submission runtime behind an internal bit-result
interface. Private interpreter data is retained internally, not published. -/
namespace ExplainableCrypto.Helios.Computational

def ballotSubmissionRuntimeBitCodec (p q : Nat) [NeZero p] [NeZero q] : BitRecordCodec
    ((RepairedSubmissionResult (ZMod q) (PrimeGroup p q) ×
      BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q)) ×
      BallotFiniteCache (ZMod q) (PrimeGroup p q)) :=
  ((ballotSubmissionBitCodec p q).pair (ballotBothCachesBitCodec p q)).equiv (Equiv.prodAssoc _ _ _).symm

theorem ballotSubmissionRuntimeBits_roundTrip {p q : Nat} [NeZero p] [NeZero q]
    (out : (RepairedSubmissionResult (ZMod q) (PrimeGroup p q) ×
      BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q)) ×
      BallotFiniteCache (ZMod q) (PrimeGroup p q)) :
    (ballotSubmissionRuntimeBitCodec p q).decode ((ballotSubmissionRuntimeBitCodec p q).encode out) = some out :=
  BitRecordCodec.roundTrip _ _

theorem ballotSubmissionRuntimeBits_exact {p q : Nat} [NeZero p] [NeZero q]
    (word : List Bool)
    (out : (RepairedSubmissionResult (ZMod q) (PrimeGroup p q) ×
      BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q)) ×
      BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (h : (ballotSubmissionRuntimeBitCodec p q).decode word = some out) :
    word = (ballotSubmissionRuntimeBitCodec p q).encode out := BitRecordCodec.exact _ _ _ h

open OracleComp OracleSpec
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]

def repairedSubmissionRuntimeBits (g pk : PrimeGroup p q) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) (PrimeGroup p q) →
      BallotOracleComp (ZMod q) (PrimeGroup p q) (Ballot (ZMod q) (PrimeGroup p q) 2)) : ProbComp (List Bool) :=
  (ballotSubmissionRuntimeBitCodec p q).encode <$>
    runBallotFiniteProgrammed g pk (repairedSubmissionPrimeOracle g pk vote attacker)

/-- Decoding the actual bit-result program exactly recovers every result and
both caches/history/flag, with the original probabilistic computation. -/
theorem repairedSubmissionRuntimeBits_decode (g pk : PrimeGroup p q) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) (PrimeGroup p q) →
      BallotOracleComp (ZMod q) (PrimeGroup p q) (Ballot (ZMod q) (PrimeGroup p q) 2)) :
    (ballotSubmissionRuntimeBitCodec p q).decode <$> repairedSubmissionRuntimeBits g pk vote attacker =
      some <$> runBallotFiniteProgrammed g pk (repairedSubmissionPrimeOracle g pk vote attacker) := by
  simp [repairedSubmissionRuntimeBits,Functor.map_map,BitRecordCodec.roundTrip]

/-- Actual supported encoded runtime results have the combined data bound.
Attacker interactions are counted, but local execution time is still unproved. -/
theorem repairedSubmissionRuntimeBits_length_le (g pk : PrimeGroup p q) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) (PrimeGroup p q) →
      BallotOracleComp (ZMod q) (PrimeGroup p q) (Ballot (ZMod q) (PrimeGroup p q) 2))
    (n m : Nat)
    (hn : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n)
    (hm : ∀ view, (attacker view).IsTotalQueryBound m)
    (word : List Bool) (hw : word ∈ support (repairedSubmissionRuntimeBits g pk vote attacker)) :
    word.length ≤ bitPairSize (submissionRecordBitBound p q 2 3)
      (bothCachesBitBound p q (m+19) (m+19) (n+15)) := by
  simp only [repairedSubmissionRuntimeBits,support_map,Set.mem_image] at hw
  obtain ⟨out,ho,rfl⟩ := hw
  exact BitRecordCodec.pair_length_le _ _ out.1.1 (out.1.2,out.2) _ _
    (repairedSubmissionPrime_output_bits_le g pk vote attacker out ho)
    (repairedSubmissionPrime_bothCaches_bits_le g pk vote attacker n m hn hm out ho)

#print axioms ballotSubmissionRuntimeBits_roundTrip
#print axioms ballotSubmissionRuntimeBits_exact
#print axioms repairedSubmissionRuntimeBits_decode
#print axioms repairedSubmissionRuntimeBits_length_le
end ExplainableCrypto.Helios.Computational
