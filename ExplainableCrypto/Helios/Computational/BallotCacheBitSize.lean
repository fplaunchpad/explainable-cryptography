import ExplainableCrypto.Helios.Computational.BallotCacheCodec
import ExplainableCrypto.Helios.Computational.RepairedReplayStorage
import ExplainableCrypto.Helios.Computational.PrimeReplay

/-! Bit lengths of complete encoded finite cache records, including framing.
The final bound uses actual source reachability to derive the entry count. -/
namespace ExplainableCrypto.Helios.Computational

def groupRecordBitBound (p : Nat) : Nat := 2*(p-1).size+1

def keyRecordBitBound (p : Nat) : Nat :=
  9+8*(2*(groupRecordBitBound p).size+1+groupRecordBitBound p)

def cacheEntryBitBound (p q : Nat) : Nat :=
  5+(2*(keyRecordBitBound p).size+1+keyRecordBitBound p)+
    (2*(groupRecordBitBound q).size+1+groupRecordBitBound q)

def cacheRecordBitBound (p q n : Nat) : Nat :=
  2*n.size+1+n*(2*(cacheEntryBitBound p q).size+1+cacheEntryBitBound p q)

variable {p q : Nat} [NeZero p] [NeZero q]

theorem ballotKeyBits_length_le (key : BallotForkPoint (PrimeGroup p q)) :
    ((ballotKeyBitCodec p q).encode key).length ≤ keyRecordBitBound p := by
  have h := bitFieldsEncode_length_le ((ballotKeyRecord key).map primeGroupEncode)
    (groupRecordBitBound p) (by
      intro w hw
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hw
      exact primeGroupEncode_length_le x)
  change (bitFieldsEncode ((ballotKeyRecord key).map primeGroupEncode)).length ≤ _
  unfold keyRecordBitBound
  simpa only [List.length_map,ballotKeyRecord_length,show (8 : Nat).size = 4 from rfl] using h

theorem ballotCacheEntryBits_length_le (entry : PrimeCacheEntry p q) :
    ((ballotCacheEntryBitCodec p q).encode entry).length ≤ cacheEntryBitBound p q := by
  change (bitFieldsEncode [(ballotKeyBitCodec p q).encode entry.1,
    (primeScalarBitCodec q).encode entry.2]).length ≤ _
  rw [bitFieldsEncode_length]
  have hk := ballotKeyBits_length_le entry.1
  have ha : ((primeScalarBitCodec q).encode entry.2).length ≤ groupRecordBitBound q :=
    scalarEncode_length_le entry.2
  have hks := Nat.size_le_size hk
  have has := Nat.size_le_size ha
  simp only [List.length_cons,List.length_nil,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,Nat.add_zero,show (2 : Nat).size = 2 from rfl]
  unfold cacheEntryBitBound
  omega

theorem ballotCacheBits_length_le (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q)) :
    ((ballotCacheBitCodec p q).encode cache).length ≤
      cacheRecordBitBound p q cache.entries.length := by
  have h := bitFieldsEncode_length_le (cache.entries.map (ballotCacheEntryBitCodec p q).encode)
    (cacheEntryBitBound p q) (by
      intro w hw
      obtain ⟨entry,_,rfl⟩ := List.mem_map.mp hw
      exact ballotCacheEntryBits_length_le entry)
  change (bitFieldsEncode (cache.entries.map (ballotCacheEntryBitCodec p q).encode)).length ≤ _
  unfold cacheRecordBitBound
  simpa only [List.length_map] using h

theorem ballotCacheBits_length_le_of_entries
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q)) (n : Nat)
    (hn : cache.entries.length ≤ n) :
    ((ballotCacheBitCodec p q).encode cache).length ≤ cacheRecordBitBound p q n := by
  have h := ballotCacheBits_length_le cache
  have hs := Nat.size_le_size hn
  have hm := Nat.mul_le_mul_right (2*(cacheEntryBitBound p q).size+1+cacheEntryBitBound p q) hn
  unfold cacheRecordBitBound at h ⊢
  omega

open OracleComp OracleSpec

/-- Actual historical finite replay states supply their own entry bound.
All fields and scalar answers are included; no cache-cover premise is added. -/
theorem repairedSubmissionFinite_cache_bits_le {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) (PrimeGroup p q) →
      BallotOracleComp (ZMod q) (PrimeGroup p q) (Ballot (ZMod q) (PrimeGroup p q) 2))
    (n : Nat) (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n)
    (out : RepairedSubmissionResult (ZMod q) (PrimeGroup p q) ×
      BallotFiniteLoggedState (ZMod q) (PrimeGroup p q))
    (ho : out ∈ support (runBallotFiniteLogged
      (repairedSubmissionFiniteSourceOracle g pk vote attacker) (∅,[]))) :
    ((ballotCacheBitCodec p q).encode out.2.1).length ≤ cacheRecordBitBound p q (n+15) := by
  exact ballotCacheBits_length_le_of_entries out.2.1 (n+15)
    (repairedSubmissionFinite_storage_le g pk vote attacker n hb out ho).2.1

/-- The explicit-nonce replay source derives the same bound from its own
query syntax. No equality of old and new replay paths is assumed. -/
theorem repairedSubmissionPrime_cache_bits_le {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) (PrimeGroup p q) →
      BallotOracleComp (ZMod q) (PrimeGroup p q) (Ballot (ZMod q) (PrimeGroup p q) 2))
    (n : Nat) (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n)
    (out : RepairedSubmissionResult (ZMod q) (PrimeGroup p q) ×
      BallotFiniteLoggedState (ZMod q) (PrimeGroup p q))
    (ho : out ∈ support (runBallotFiniteLogged
      (repairedSubmissionPrimeSourceOracle g pk vote attacker) (∅,[]))) :
    ((ballotCacheBitCodec p q).encode out.2.1).length ≤ cacheRecordBitBound p q (n+15) := by
  apply ballotCacheBits_length_le_of_entries out.2.1 (n+15)
  have h := runBallotFiniteLogged_cache_length_le _ (n+15)
    (repairedSubmissionPrimeSource_query_bound g pk vote attacker n hb) (∅,[]) out ho
  simpa only [AList.empty_entries,List.length_nil,Nat.zero_add] using h

#print axioms repairedSubmissionPrime_cache_bits_le
#print axioms ballotKeyBits_length_le
#print axioms ballotCacheEntryBits_length_le
#print axioms ballotCacheBits_length_le
#print axioms ballotCacheBits_length_le_of_entries
#print axioms repairedSubmissionFinite_cache_bits_le
end ExplainableCrypto.Helios.Computational
