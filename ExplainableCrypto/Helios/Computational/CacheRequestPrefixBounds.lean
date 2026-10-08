import ExplainableCrypto.Helios.Computational.CacheRequestPrefixes
import ExplainableCrypto.Helios.Computational.CacheRequestPolynomial

/-! Specialize the executed request's size and cost bounds to original-source
prestates. The only source hypothesis is its hash-query budget; intermediate
cache/log counts are derived. Uniform requests are captured too, but their
arbitrary range widths are not bounded by the hash-request theorem below. -/
namespace ExplainableCrypto.Helios.Computational.CacheRequestPrefixes
open OracleComp OracleSpec
attribute [local irreducible] CacheRequestMachine.code CacheRequestMachine.clock
  CacheRequestMachine.cost
variable {p q : Nat} [NeZero p] [NeZero q] {A : Type}

/-- Public widths and source-derived entry counts bound the complete request
clock. This includes framing, sampler operands and both cache/log payloads. -/
def requestBound (p q c l slack : Nat) : Nat :=
  1000000*(TM2TapeRuns.codeAccesses CacheRoutineCode.readCode+1)*
    (p.size+q.size+keyRecordBitBound p+cacheRecordBitBound p q c+
      bitListSize (keyRecordBitBound p) l+slack+1)^3

private theorem size_self (n : Nat) : n.size ≤ n := Nat.size_le.mpr n.lt_two_pow_self

/-- Polynomial public widths, initial-offset-plus-query counts and sampling
slack suffice for a polynomial request bound. Codec/header sizes are derived,
not additional family assumptions. -/
theorem requestBound_polynomial (p q c l slack : Nat → Nat)
    (P Q C L S : Polynomial Nat)
    (hp : ∀ n, (p n).size ≤ P.eval n) (hq : ∀ n, (q n).size ≤ Q.eval n)
    (hc : ∀ n, c n ≤ C.eval n) (hl : ∀ n, l n ≤ L.eval n)
    (hs : ∀ n, slack n ≤ S.eval n) :
    ∃ R : Polynomial Nat, ∀ n,
      requestBound (p n) (q n) (c n) (l n) (slack n) ≤ R.eval n := by
  let K : Polynomial Nat := Polynomial.C 48*P+Polynomial.C 41
  let E : Polynomial Nat := Polynomial.C 7+Polynomial.C 3*K+
    Polynomial.C 3*(Polynomial.C 2*Q+1)
  let BC : Polynomial Nat := Polynomial.C 2*C+1+C*(Polynomial.C 3*E+1)
  let BL : Polynomial Nat := Polynomial.C 2*L+1+L*(Polynomial.C 3*K+1)
  refine ⟨Polynomial.C (1000000*(TM2TapeRuns.codeAccesses CacheRoutineCode.readCode+1))*
    (P+Q+K+BC+BL+S+1)^3,?_⟩
  intro n
  have hg (a : Nat) : groupRecordBitBound a ≤ 2*a.size+1 := by
    have h := Nat.size_le_size (Nat.sub_le a 1)
    unfold groupRecordBitBound
    omega
  have hk : keyRecordBitBound (p n) ≤ K.eval n := by
    have h := hg (p n)
    have h' := size_self (groupRecordBitBound (p n))
    have hp' := hp n
    simp only [K,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
    unfold keyRecordBitBound
    omega
  have he : cacheEntryBitBound (p n) (q n) ≤ E.eval n := by
    have h := hg (q n)
    have hq' := hq n
    have h' := size_self (groupRecordBitBound (q n))
    have h'' := size_self (keyRecordBitBound (p n))
    simp only [E,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_one]
    unfold cacheEntryBitBound
    omega
  have hcb : cacheRecordBitBound (p n) (q n) (c n) ≤ BC.eval n := by
    have hh := size_self (cacheEntryBitBound (p n) (q n))
    have hn := size_self (c n)
    have hfactor : 2*(cacheEntryBitBound (p n) (q n)).size+1+
        cacheEntryBitBound (p n) (q n) ≤ 3*E.eval n+1 := by omega
    have hm := Nat.mul_le_mul (hc n) hfactor
    have hc' := hc n
    simp only [BC,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_one]
    unfold cacheRecordBitBound
    omega
  have hlb : bitListSize (keyRecordBitBound (p n)) (l n) ≤ BL.eval n := by
    have hh := size_self (keyRecordBitBound (p n))
    have hn := size_self (l n)
    have hfactor : 2*(keyRecordBitBound (p n)).size+1+
        keyRecordBitBound (p n) ≤ 3*K.eval n+1 := by omega
    have hm := Nat.mul_le_mul (hl n) hfactor
    have hl' := hl n
    simp only [BL,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_one]
    unfold bitListSize
    omega
  unfold requestBound
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_one]
  gcongr
  · exact hp n
  · exact hq n
  · exact hs n

/-- Bit lengths at every captured original request, including the initial
storage offsets and the outer count headers. -/
theorem encoded_prestates_bound
    (oa : BallotOracleComp (ZMod q) (PrimeGroup p q) A) (n : Nat)
    (hb : oa.IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n)
    (s : BallotFiniteLoggedState (ZMod q) (PrimeGroup p q))
    (out : A × State (ZMod q) (PrimeGroup p q))
    (ho : out ∈ support (run oa s)) :
    ∀ e ∈ out.2.2,
      ((ballotCacheBitCodec p q).encode e.2.1).length ≤
        cacheRecordBitBound p q (s.1.entries.length+n) ∧
      (((ballotLogEntryBitCodec p q).list).encode e.2.2).length ≤
        bitListSize (keyRecordBitBound p) (s.2.length+n) := by
  intro e he
  have h := prestates_bound oa n hb s out ho e he
  exact ⟨ballotCacheBits_length_le_of_entries _ _ h.1,
    BitRecordCodec.list_length_le _ _ _ _ (fun x _ => ballotKeyBits_length_le x.2) h.2⟩

/-- At each actual source prestate, every typed hash key has a bounded executed
request clock. No bound on an intermediate cache or log is supplied by the caller. -/
theorem request_clock_bound
    (oa : BallotOracleComp (ZMod q) (PrimeGroup p q) A) (n : Nat)
    (hb : oa.IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n)
    (s : BallotFiniteLoggedState (ZMod q) (PrimeGroup p q))
    (out : A × State (ZMod q) (PrimeGroup p q))
    (ho : out ∈ support (run oa s)) (e : Event (ZMod q) (PrimeGroup p q))
    (he : e ∈ out.2.2) (key : BallotForkPoint (PrimeGroup p q)) (slack : Nat) :
    CacheRequestMachine.clock e.2.1 key e.2.2 slack ≤
      requestBound p q (s.1.entries.length+n) (s.2.length+n) slack := by
  have h := encoded_prestates_bound oa n hb s out ho e he
  apply (CacheRequestMachine.clock_le_loaded e.2.1 key e.2.2 slack).trans
  apply (CacheRequestMachine.loadedClock_le_cubic _ _ _ _ _ _).trans
  unfold requestBound
  gcongr
  · exact ballotKeyBits_length_le key
  · exact h.1
  · exact h.2

/-- Every actual machine leaf for a hash request captured in the source halts
and has the source-derived charge bound. The source event determines the key;
this theorem does not assert compilation of its enclosing continuation. -/
theorem hash_request_execution_bound
    (oa : BallotOracleComp (ZMod q) (PrimeGroup p q) A) (n : Nat)
    (hb : oa.IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n)
    (s : BallotFiniteLoggedState (ZMod q) (PrimeGroup p q))
    (out : A × State (ZMod q) (PrimeGroup p q))
    (ho : out ∈ support (run oa s))
    (before : BallotFiniteLoggedState (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (he : (Sum.inr key,before) ∈ out.2.2)
    (slack : Nat) :
    ∀ leaf ∈ support (BitOracleMachine.run CacheRequestMachine.code
      (CacheRequestMachine.clock before.1 key before.2 slack)
      (CacheRequestMachine.start (CacheRequestMachine.input before.1 key before.2 slack))),
      leaf.1.l = none ∧ leaf.2 ≤
        32*requestBound p q (s.1.entries.length+n) (s.2.length+n) slack := by
  intro leaf hl
  have h := (CacheRequestMachine.request_run before.1 key before.2 slack).2 leaf hl
  refine ⟨h.1,h.2.trans ?_⟩
  apply (CacheRequestMachine.cost_le_clock before.1 key before.2 slack).trans
  exact Nat.mul_le_mul_left 32 (request_clock_bound oa n hb s out ho _ he key slack)

/-- The historical explicit-nonce source supplies its own n+15 hash budget at
all captured request boundaries, not merely at its final state. -/
theorem repaired_source_request_clock_bound [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) (PrimeGroup p q) →
      BallotOracleComp (ZMod q) (PrimeGroup p q) (Ballot (ZMod q) (PrimeGroup p q) 2))
    (n : Nat) (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n)
    (out : RepairedSubmissionResult (ZMod q) (PrimeGroup p q) × State (ZMod q) (PrimeGroup p q))
    (ho : out ∈ support (run (repairedSubmissionPrimeSourceOracle g pk vote attacker) (∅,[])))
    (e : Event (ZMod q) (PrimeGroup p q)) (he : e ∈ out.2.2)
    (key : BallotForkPoint (PrimeGroup p q)) (slack : Nat) :
    CacheRequestMachine.clock e.2.1 key e.2.2 slack ≤ requestBound p q (n+15) (n+15) slack := by
  have h := request_clock_bound _ (n+15)
    (repairedSubmissionPrimeSource_query_bound g pk vote attacker n hb) (∅,[]) out ho e he key slack
  simpa only [AList.empty_entries,List.length_nil,Nat.zero_add] using h

#print axioms requestBound_polynomial
#print axioms encoded_prestates_bound
#print axioms request_clock_bound
#print axioms hash_request_execution_bound
#print axioms repaired_source_request_clock_bound
end ExplainableCrypto.Helios.Computational.CacheRequestPrefixes
