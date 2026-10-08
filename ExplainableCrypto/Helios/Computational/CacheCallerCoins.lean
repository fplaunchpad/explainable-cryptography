import ExplainableCrypto.Helios.Computational.CacheHashCoins
import ExplainableCrypto.Helios.Computational.FairBitUniformOracle

/-! Complete adaptive callers with executed cache sampling. Codecs and source
continuations are host functions here; physical transfers and their costs remain
separate obligations. The reference is the original finite logged source. -/
namespace ExplainableCrypto.Helios.Computational.CacheCallerCoins
open OracleComp OracleSpec
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

variable {p q : Nat} [NeZero p] [NeZero q]

def encode {A : Type} (out : A × CacheHashCoins.State p q) :=
  (out.1,(ballotCacheBitCodec p q).encode out.2.1,CacheHashHandler.logEncode out.2.2)

/-- Decode only the actual produced word, retaining explicit malformed failure. -/
def sampleIndex (q slack : Nat) [NeZero q] : OracleComp coinSpec (Option (Fin q)) :=
  (fun word => ((primeScalarBitCodec q).decode word).map (ZMod.finEquiv q).symm) <$>
    CacheHashCoins.sample q (List.replicate (q.size+slack) true)

theorem sampleIndex_eq (q slack : Nat) [NeZero q] :
    sampleIndex q slack = some <$> sampleFairBitRange q slack := by
  rw [sampleIndex,CacheHashCoins.sample_eq]
  simp only [List.length_replicate,Functor.map_map,sampleFairBitRange]
  congr 1
  funext a
  have he : uniformNatEncode a.val = (primeScalarBitCodec q).encode ((ZMod.finEquiv q) a) := by
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q => rfl
  simp [he,BitRecordCodec.roundTrip]

/-- Execute the original inclusive upper-bound convention, including t+1. -/
def sampleUpper (t slack : Nat) : OracleComp coinSpec (Option (Fin (t+1))) :=
  (fun word => ((primeScalarBitCodec (t+1)).decode word).map (ZMod.finEquiv (t+1)).symm) <$>
    CacheHashCoins.prepared true slack t

theorem sampleUpper_eq (t slack : Nat) :
    sampleUpper t slack = some <$> sampleFairBitRange (t+1) slack := by
  have : NeZero (SamplerOperands.range true t) := inferInstanceAs (NeZero (t+1))
  rw [sampleUpper,CacheHashCoins.prepared_eq]
  dsimp only [SamplerOperands.range]
  rw [Functor.map_map]
  congr 1
  funext a
  have he : uniformNatEncode a.val =
      (primeScalarBitCodec (t+1)).encode ((ZMod.finEquiv (t+1)) a) := rfl
  simp [he,BitRecordCodec.roundTrip]

/-- The actual finite uniform source lowers to the existing fair-bit range
sampler, preserving the complete query tree. -/
theorem uniform_eq (q slack : Nat) [NeZero q] :
    runFairBitUniform slack (uniformSample (Fin q)) = sampleFairBitRange q slack := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    change simulateQ (fairBitUniformImpl slack) (liftM (unifSpec.query q)) = _
    simp [fairBitUniformImpl]

private theorem fair_bind {A B : Type} (slack : Nat) (oa : ProbComp A) (next : A → ProbComp B) :
    runFairBitUniform slack (oa >>= next) =
      (runFairBitUniform slack oa >>= fun a => runFairBitUniform slack (next a)) := by
  simp only [runFairBitUniform,simulateQ_bind]

/-- Both uniform-range requests and hash misses use the executed scalar program.
Canonical decoding supplies typed source continuations, without dropping cache/log.
Serialized input construction, routine loading and continuation invocation
remain host operations; the sampler executes width/modulus preparation. -/
def run {A : Type} (slack : Nat) (oa : BallotOracleComp (ZMod q) (PrimeGroup p q) A) :
    List Bool → List Bool → OracleComp coinSpec (Option (A × (List Bool × List Bool))) :=
  OracleComp.construct (fun a word log => pure (some (a,word,log)))
    (fun t _ rec => match t with
      | .inl n => fun word log => do
        let result ← sampleUpper n slack
        match result with
        | none => pure none
        | some a => rec a word log
      | .inr key => fun word log => do
        let result ← CacheHashCoins.hashPrepared p q slack
          ((ballotKeyBitCodec p q).encode key) word log
        match result with
        | none => pure none
        | some (value,word',log') =>
          match (primeScalarBitCodec q).decode value with
          | none => pure none
          | some a => rec a word' log') oa

/-- Exact source distribution before replacing any of its private range samples. -/
def source {A : Type} (oa : BallotOracleComp (ZMod q) (PrimeGroup p q) A)
    (s : CacheHashCoins.State p q) : ProbComp (A × CacheHashCoins.State p q) :=
  simulateQ CacheHashCoins.exactChallenge (runBallotFiniteLogged oa s)

omit [NeZero p] in
private theorem source_uniform {A : Type} (n : Nat)
    (next : Fin (n+1) → BallotOracleComp (ZMod q) (PrimeGroup p q) A)
    (s : CacheHashCoins.State p q) :
    source (liftM ((BallotOracleSpec (ZMod q) (PrimeGroup p q)).query (.inl n)) >>= next) s =
      (liftM (unifSpec.query n) >>= fun a => source (next a) s) := by
  simp only [source,runBallotFiniteLogged,run_simulateQ_query_bind]
  have he : (ballotFiniteLoggedImpl (F := ZMod q) (G := PrimeGroup p q) (.inl n)).run s =
      (FiatShamir.Fork.wrappedUniformQuery (ZMod q) n >>= fun a => pure (a,s)) := rfl
  rw [he]
  simp only [bind_assoc,pure_bind,simulateQ_bind]
  rfl

omit [NeZero p] in
private theorem source_hash {A : Type} (key : BallotForkPoint (PrimeGroup p q))
    (next : ZMod q → BallotOracleComp (ZMod q) (PrimeGroup p q) A)
    (s : CacheHashCoins.State p q) :
    source (liftM ((BallotOracleSpec (ZMod q) (PrimeGroup p q)).query (.inr key)) >>= next) s =
      (match s.1.lookup key with
      | some a => source (next a) s
      | none => uniformSample (Fin q) >>= fun a => source (next ((ZMod.finEquiv q) a))
          (s.1.insert key ((ZMod.finEquiv q) a),s.2++[((),key)])) := by
  simp only [source,runBallotFiniteLogged,run_simulateQ_query_bind]
  cases hh : s.1.lookup key with
  | some a => simp [ballotFiniteLoggedImpl,QueryImpl.add,StateT.run,hh]
  | none => simp [ballotFiniteLoggedImpl,QueryImpl.add,StateT.run,hh,
      FiatShamir.Fork.wrappedChallengeQuery,CacheHashCoins.exactChallenge]

attribute [local irreducible] CacheHashCoins.hash CacheHashCoins.hashPrepared sampleIndex sampleUpper

set_option maxHeartbeats 800000 in
/-- Every adaptive source caller agrees as a complete coin-query tree with the
existing fair-bit interpretation of its original exact finite logged source.
Initial-state encoding and successor correspondence are derived for all states. -/
theorem run_eq {A : Type} (slack : Nat)
    (oa : BallotOracleComp (ZMod q) (PrimeGroup p q) A) (s : CacheHashCoins.State p q) :
    run slack oa ((ballotCacheBitCodec p q).encode s.1) (CacheHashHandler.logEncode s.2) =
      (fun out => some (encode out)) <$> runFairBitUniform slack (source oa s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    change pure (some (a,(ballotCacheBitCodec p q).encode s.1,CacheHashHandler.logEncode s.2)) = _
    simp [source,runBallotFiniteLogged,runFairBitUniform,encode]
  | query_bind t next ih =>
    cases t with
    | inl n =>
      rw [source_uniform]
      change (sampleUpper n slack >>= fun result => match result with
        | none => pure none
        | some a => run slack (next a) ((ballotCacheBitCodec p q).encode s.1)
            (CacheHashHandler.logEncode s.2)) = _
      rw [sampleUpper_eq,bind_map_left]
      simp only [runFairBitUniform,simulateQ_bind,simulateQ_query,fairBitUniformImpl,map_bind,OracleQuery.cont_query,OracleQuery.input_query,id_map]
      apply bind_congr
      intro a
      exact ih a s
    | inr key =>
      rw [source_hash]
      change (CacheHashCoins.hashPrepared p q slack
        ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode s.1)
        (CacheHashHandler.logEncode s.2) >>= fun result => match result with
          | none => pure none
          | some (value,w,l) => match (primeScalarBitCodec q).decode value with
            | none => pure none
            | some a => run slack (next a) w l) = _
      rw [CacheHashCoins.hashPrepared_eq]
      cases hh : s.1.lookup key with
      | some a =>
        rw [CacheHashCoins.hash_hit _ key s a hh]
        simpa [CacheHashCoins.encode,BitRecordCodec.roundTrip] using ih a s
      | none =>
        rw [CacheHashCoins.hash_miss _ key s hh,bind_map_left]
        simp only [CacheHashCoins.encode,BitRecordCodec.roundTrip,List.length_replicate]
        rw [fair_bind,uniform_eq]
        rw [map_bind]
        apply bind_congr
        intro a
        exact ih ((ZMod.finEquiv q) a)
          (s.1.insert key ((ZMod.finEquiv q) a),s.2++[((),key)])

omit [NeZero p] in
/-- Exact-source range requests are bounded by the original caller's requests.
Hits cost no draw; misses and ordinary range requests cost one. -/
theorem source_bound {A : Type}
    (oa : BallotOracleComp (ZMod q) (PrimeGroup p q) A)
    (s : CacheHashCoins.State p q) (B : Nat) (hb : oa.IsTotalQueryBound B) :
    (source oa s).IsTotalQueryBound B := by
  induction oa using OracleComp.inductionOn generalizing s B with
  | pure a => simp only [source,runBallotFiniteLogged,simulateQ_pure,StateT.run_pure]; trivial
  | query_bind t next ih =>
    rw [isTotalQueryBound_query_bind_iff] at hb
    cases B with
    | zero => omega
    | succ B =>
      cases t with
      | inl n =>
        rw [source_uniform,isTotalQueryBound_query_bind_iff]
        exact ⟨by omega,fun a => ih a s B (by simpa using hb.2 a)⟩
      | inr key =>
        rw [source_hash]
        cases hh : s.1.lookup key with
        | some a => exact (ih a s B (by simpa using hb.2 a)).mono (by omega)
        | none =>
          have hu : (uniformSample (Fin q)).IsTotalQueryBound 1 := by
            cases q with
            | zero => exact (NeZero.ne 0 rfl).elim
            | succ q =>
              change (liftM (unifSpec.query q) >>= pure : ProbComp (Fin (q+1))).IsTotalQueryBound 1
              rw [isTotalQueryBound_query_bind_iff]
              exact ⟨by decide,fun _ => trivial⟩
          simpa only [Nat.add_comm 1 B] using isTotalQueryBound_bind hu (fun a =>
            ih ((ZMod.finEquiv q) a)
              (s.1.insert key ((ZMod.finEquiv q) a),s.2++[((),key)]) B
              (by simpa using hb.2 ((ZMod.finEquiv q) a)))

/-- Full return/cache/log error for the complete caller, reusing the established
adaptive sampling theorem. B bounds original caller requests, not runtime. -/
theorem distance {A : Type} (slack : Nat)
    (oa : BallotOracleComp (ZMod q) (PrimeGroup p q) A) (s : CacheHashCoins.State p q)
    (B : Nat) (hb : oa.IsTotalQueryBound B) :
    SPMF.tvDist
      (evalSPMF (run slack oa ((ballotCacheBitCodec p q).encode s.1)
        (CacheHashHandler.logEncode s.2)))
      (evalSPMF ((fun out => some (encode out)) <$> source oa s)) ≤
        (B : ℝ)*((2 : ℝ)^slack)⁻¹ := by
  rw [run_eq,evalSPMF_map,evalSPMF_map]
  exact (SPMF.tvDist_map_le _ _ _).trans (runFairBitUniform_tv_le slack _ B (source_bound oa s B hb))

#print axioms uniform_eq

end ExplainableCrypto.Helios.Computational.CacheCallerCoins
