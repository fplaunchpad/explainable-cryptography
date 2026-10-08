import ExplainableCrypto.Helios.Computational.BallotStateCodec
import ExplainableCrypto.Helios.Computational.BallotCacheBitSize
import ExplainableCrypto.Helios.Computational.RepairedShadowStorage
import ExplainableCrypto.Helios.Computational.PrimeReplayCost

/-! Complete finite-state record lengths, including both caches, ordered
histories and the collision flag. These bounds do not measure machine time. -/
namespace ExplainableCrypto.Helios.Computational

def bitPairSize (a b : Nat) : Nat := 5+(2*a.size+1+a)+(2*b.size+1+b)
def bitListSize (a n : Nat) : Nat := 2*n.size+1+n*(2*a.size+1+a)

theorem BitRecordCodec.pair_length_le {A B : Type} (c : BitRecordCodec A) (d : BitRecordCodec B)
    (x : A) (y : B) (a b : Nat) (ha : (c.encode x).length ≤ a) (hb : (d.encode y).length ≤ b) :
    ((c.pair d).encode (x,y)).length ≤ bitPairSize a b := by
  change (bitFieldsEncode [c.encode x,d.encode y]).length ≤ _
  rw [bitFieldsEncode_length]
  have hsa := Nat.size_le_size ha
  have hsb := Nat.size_le_size hb
  simp only [List.length_cons,List.length_nil,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,Nat.add_zero,show (2 : Nat).size = 2 from rfl]
  unfold bitPairSize
  omega

theorem BitRecordCodec.list_length_le {A : Type} (c : BitRecordCodec A) (xs : List A) (a n : Nat)
    (ha : ∀ x ∈ xs, (c.encode x).length ≤ a) (hn : xs.length ≤ n) :
    (c.list.encode xs).length ≤ bitListSize a n := by
  have h := bitFieldsEncode_length_le (xs.map c.encode) a (by
    intro w hw
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hw
    exact ha x hx)
  simp only [List.length_map] at h
  have hs := Nat.size_le_size hn
  have hm := Nat.mul_le_mul_right (2*a.size+1+a) hn
  change (bitFieldsEncode (xs.map c.encode)).length ≤ _
  unfold bitListSize
  omega

def statementRecordBitBound (p : Nat) : Nat :=
  bitPairSize (bitPairSize (groupRecordBitBound p) (groupRecordBitBound p))
    (bitPairSize (groupRecordBitBound p) (groupRecordBitBound p))

def loggedStateBitBound (p q c l : Nat) : Nat :=
  bitPairSize (cacheRecordBitBound p q c) (bitListSize (keyRecordBitBound p) l)

def programmedStateBitBound (p q c h : Nat) : Nat :=
  bitPairSize (cacheRecordBitBound p q c) (bitPairSize 1 (bitListSize (statementRecordBitBound p) h))

def bothCachesBitBound (p q c h l : Nat) : Nat :=
  bitPairSize (programmedStateBitBound p q c h) (cacheRecordBitBound p q l)

variable {p q : Nat} [NeZero p] [NeZero q]

theorem ballotStatementBits_length_le (s : BallotStatement (PrimeGroup p q)) :
    ((ballotStatementBitCodec p q).encode s).length ≤ statementRecordBitBound p := by
  have hp (x y : PrimeGroup p q) := BitRecordCodec.pair_length_le (primeGroupBitCodec p q) (primeGroupBitCodec p q)
    x y (groupRecordBitBound p) (groupRecordBitBound p)
    (primeGroupEncode_length_le x) (primeGroupEncode_length_le y)
  exact BitRecordCodec.pair_length_le _ _ (s.generator,s.publicKey) s.ciphertext _ _
    (hp s.generator s.publicKey) (hp s.ciphertext.1 s.ciphertext.2)

theorem ballotLoggedBits_length_le (s : BallotFiniteLoggedState (ZMod q) (PrimeGroup p q))
    (c l : Nat) (hc : s.1.entries.length ≤ c) (hl : s.2.length ≤ l) :
    ((ballotLoggedBitCodec p q).encode s).length ≤ loggedStateBitBound p q c l := by
  exact BitRecordCodec.pair_length_le _ _ s.1 s.2 _ _ (ballotCacheBits_length_le_of_entries s.1 c hc)
    (BitRecordCodec.list_length_le _ s.2 _ l (fun e _ => ballotKeyBits_length_le e.2) hl)

theorem ballotProgrammedBits_length_le
    (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q)) (c h : Nat)
    (hc : s.cache.entries.length ≤ c) (hh : s.programmed.length ≤ h) :
    ((ballotProgrammedBitCodec p q).encode s).length ≤ programmedStateBitBound p q c h := by
  exact BitRecordCodec.pair_length_le _ _ s.cache (s.bad,s.programmed) _ _
    (ballotCacheBits_length_le_of_entries s.cache c hc)
    (BitRecordCodec.pair_length_le ballotBoolBitCodec _ s.bad s.programmed 1 _ (by rfl)
      (BitRecordCodec.list_length_le _ s.programmed _ h (fun stmt _ => ballotStatementBits_length_le stmt) hh))

theorem ballotBothCachesBits_length_le
    (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q) ×
      BallotFiniteCache (ZMod q) (PrimeGroup p q)) (c h l : Nat)
    (hc : s.1.cache.entries.length ≤ c) (hh : s.1.programmed.length ≤ h)
    (hl : s.2.entries.length ≤ l) :
    ((ballotBothCachesBitCodec p q).encode s).length ≤ bothCachesBitBound p q c h l := by
  exact BitRecordCodec.pair_length_le _ _ s.1 s.2 _ _ (ballotProgrammedBits_length_le s.1 c h hc hh)
    (ballotCacheBits_length_le_of_entries s.2 l hl)

open OracleComp OracleSpec

/-- Reachability in the explicit replay source derives both log/cache counts. -/
theorem repairedSubmissionPrime_logged_bits_le {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) (PrimeGroup p q) →
      BallotOracleComp (ZMod q) (PrimeGroup p q) (Ballot (ZMod q) (PrimeGroup p q) 2))
    (n : Nat) (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n)
    (out : RepairedSubmissionResult (ZMod q) (PrimeGroup p q) ×
      BallotFiniteLoggedState (ZMod q) (PrimeGroup p q))
    (ho : out ∈ support (runBallotFiniteLogged
      (repairedSubmissionPrimeSourceOracle g pk vote attacker) (∅,[]))) :
    ((ballotLoggedBitCodec p q).encode out.2).length ≤ loggedStateBitBound p q (n+15) (n+15) := by
  have hb' := repairedSubmissionPrimeSource_query_bound g pk vote attacker n hb
  have hc := runBallotFiniteLogged_cache_length_le _ (n+15) hb' (∅,[]) out ho
  have hl := runBallotFiniteLogged_log_length_le _ (n+15) hb' (∅,[]) out ho
  apply ballotLoggedBits_length_le out.2 (n+15) (n+15)
  · simpa only [AList.empty_entries,List.length_nil,Nat.zero_add] using hc
  · simpa only [List.length_nil,Nat.zero_add] using hl

/-- The complete explicit-nonce runtime derives shadow/history and live-cache
bounds from its own budgets; both caches and every request remain encoded. -/
theorem repairedSubmissionPrime_bothCaches_bits_le {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) (PrimeGroup p q) →
      BallotOracleComp (ZMod q) (PrimeGroup p q) (Ballot (ZMod q) (PrimeGroup p q) 2))
    (n m : Nat)
    (hn : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n)
    (hm : ∀ view, (attacker view).IsTotalQueryBound m)
    (out : (RepairedSubmissionResult (ZMod q) (PrimeGroup p q) ×
      BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q)) ×
      BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (ho : out ∈ support (runBallotFiniteProgrammed g pk
      (repairedSubmissionPrimeOracle g pk vote attacker))) :
    ((ballotBothCachesBitCodec p q).encode (out.1.2,out.2)).length ≤
      bothCachesBitBound p q (m+19) (m+19) (n+15) := by
  have hraw : out.1 ∈ support ((simulateQ (ballotFiniteProgrammedImpl g pk)
      (repairedSubmissionPrimeOracle g pk vote attacker)).run .empty) := by
    apply support_simulateQ_run'_subset ballotFiniteCacheImpl _ ∅
    rw [StateT.run'_eq,support_map]
    exact Set.mem_image_of_mem Prod.fst ho
  have hs := runBallotFiniteProgrammed_storage_le g pk _ (m+19)
    (repairedSubmissionPrimeOracle_total_bound g pk vote attacker m hm) .empty out.1 hraw
  simp only [BallotFiniteProgrammedState.empty,AList.empty_entries,List.length_nil,Nat.zero_add] at hs
  have hbudget : ((simulateQ (ballotFiniteProgrammedImpl g pk)
      (repairedSubmissionPrimeOracle g pk vote attacker)).run .empty).IsQueryBoundP
      (isBallotHashQuery (F := ZMod q)) (n+15) := by
    simpa only [repairedSubmissionPrimeSourceOracle,isQueryBoundP_map_iff] using
      repairedSubmissionPrimeSource_query_bound g pk vote attacker n hn
  have hl := runBallotFiniteCache_length_le _ (n+15) hbudget ∅ out ho
  simp only [AList.empty_entries,List.length_nil,Nat.zero_add] at hl
  exact ballotBothCachesBits_length_le (out.1.2,out.2) (m+19) (m+19) (n+15) hs.1 hs.2 hl

#print axioms BitRecordCodec.pair_length_le
#print axioms BitRecordCodec.list_length_le
#print axioms ballotStatementBits_length_le
#print axioms ballotLoggedBits_length_le
#print axioms ballotProgrammedBits_length_le
#print axioms ballotBothCachesBits_length_le
#print axioms repairedSubmissionPrime_logged_bits_le
#print axioms repairedSubmissionPrime_bothCaches_bits_le
end ExplainableCrypto.Helios.Computational
