import ExplainableCrypto.Helios.Computational.StrongBallotOracle
import ExplainableCrypto.Helios.Computational.BallotSigmaProgramming

/-! The witness-free ballot simulator programs only fresh strong-hash inputs.
An existing answer is preserved and the returned proof is flagged as bad.
This defines the actual stateful step; its adaptive distance/extraction proof
must account for flagged executions rather than discarding them. -/

namespace ExplainableCrypto.Helios.Computational

open OracleComp OracleSpec
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

def strongBallotSimOracle (stmt : BallotStatement G) :
    StateT (BallotOracleCache F G) ProbComp (Proof01 F G × Bool) := fun cache => do
  let t ← ballotFullSimTranscript (F := F) stmt
  let p := ballotTranscriptProof t.1 t.2.1 t.2.2
  match cache (stmt,t.1) with
  | some _ => pure ((p,true),cache)
  | none => pure ((p,false),cache.cacheQuery (stmt,t.1) t.2.1)

omit [Fintype F] [DecidableEq F] [DecidableEq G] in
private theorem simulated_transcript_valid (stmt : BallotStatement G)
    (t : BallotCommitment G × F × BallotResponse F)
    (ht : t ∈ support (ballotFullSimTranscript (F := F) stmt)) :
    (ballotTranscriptProof t.1 t.2.1 t.2.2).Valid (fun _ => t.2.1)
      stmt.generator stmt.publicKey stmt.ciphertext := by
  simp only [ballotFullSimTranscript, support_bind, support_pure, Set.mem_iUnion,
    Set.mem_singleton_iff] at ht
  obtain ⟨c, _, e, _, z₀, _, z₁, _, rfl⟩ := ht
  exact ballotSimCommit_valid stmt c (e,z₀,z₁)

omit [Fintype F] in
theorem strongBallotSimOracle_unflagged_valid (stmt : BallotStatement G)
    (cache : BallotOracleCache F G) (out : (Proof01 F G × Bool) × BallotOracleCache F G)
    (hout : out ∈ support ((strongBallotSimOracle (F := F) stmt).run cache))
    (hbad : out.1.2 = false) :
    runBallotOracle (strongBallotVerifyOracle stmt out.1.1) out.2 = pure (true,out.2) := by
  simp only [strongBallotSimOracle, StateT.run, support_bind, Set.mem_iUnion] at hout
  obtain ⟨t, ht, hout⟩ := hout
  have hv := simulated_transcript_valid stmt t ht
  cases hc : cache (stmt,t.1) with
  | some c => simp [hc] at hout; subst out; contradiction
  | none =>
    simp only [hc, support_pure, Set.mem_singleton_iff] at hout
    subst out
    rw [runBallotOracle_verify_cached stmt _ _ t.2.1 (by
      simp [Proof01.commitment, ballotTranscriptProof])]
    simp [hv]

omit [Fintype F] [DecidableEq F] in
theorem strongBallotSimOracle_cache_le (stmt : BallotStatement G)
    (cache : BallotOracleCache F G) (out : (Proof01 F G × Bool) × BallotOracleCache F G)
    (hout : out ∈ support ((strongBallotSimOracle (F := F) stmt).run cache)) :
    cache ≤ out.2 := by
  simp only [strongBallotSimOracle, StateT.run, support_bind, Set.mem_iUnion] at hout
  obtain ⟨t, _, hout⟩ := hout
  cases hc : cache (stmt,t.1) with
  | some c =>
    simp only [hc, support_pure, Set.mem_singleton_iff] at hout
    subst out
    exact le_rfl
  | none =>
    simp only [hc, support_pure, Set.mem_singleton_iff] at hout
    subst out
    exact QueryCache.le_cacheQuery cache hc

omit [Fintype F] [DecidableEq F] in
/-- The bad flag records a prior query; even an agreeing prior answer is flagged.
This conservative event leaves all collision executions in the experiment. -/
theorem strongBallotSimOracle_bad_probability (stmt : BallotStatement G)
    (cache : BallotOracleCache F G) :
    Pr[fun out => out.1.2 = true | (strongBallotSimOracle (F := F) stmt).run cache] =
      Pr[fun t => (cache (stmt,t.1)).isSome = true | ballotFullSimTranscript (F := F) stmt] := by
  unfold strongBallotSimOracle StateT.run
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro t
  cases cache (stmt,t.1) <;> simp

omit [DecidableEq F] in
theorem strongBallotSimOracle_bad_probability_le (stmt : BallotStatement G)
    (hg : Function.Injective (fun r : F => r • stmt.generator))
    (cache : BallotOracleCache F G) (queries : Finset (BallotStatement G × BallotCommitment G))
    (hcover : ∀ key, (cache key).isSome = true → key ∈ queries) :
    Pr[fun out => out.1.2 = true | (strongBallotSimOracle (F := F) stmt).run cache] ≤
      queries.card * (Fintype.card F : ENNReal)⁻¹ := by
  rw [strongBallotSimOracle_bad_probability]
  exact (probEvent_mono (fun t _ ht => hcover (stmt,t.1) ht)).trans
    (ballotSim_query_collision_le stmt hg queries)

omit [Fintype F] [DecidableEq F] in
/-- Simulation can change only a key carrying its actual requested statement.
This is the local provenance fact needed by the programmed-cache adapter. -/
theorem strongBallotSimOracle_other_statement
    (stmt : BallotStatement G) (cache : BallotOracleCache F G)
    (out : (Proof01 F G × Bool) × BallotOracleCache F G)
    (hout : out ∈ support ((strongBallotSimOracle (F := F) stmt).run cache))
    (key : BallotStatement G × BallotCommitment G) (hne : key.1 ≠ stmt) :
    out.2 key = cache key := by
  simp only [strongBallotSimOracle, StateT.run, support_bind, Set.mem_iUnion] at hout
  obtain ⟨t,_,hout⟩ := hout
  cases hc : cache (stmt,t.1) with
  | some c =>
    simp only [hc,support_pure,Set.mem_singleton_iff] at hout
    subst out; rfl
  | none =>
    simp only [hc,support_pure,Set.mem_singleton_iff] at hout
    subst out
    exact QueryCache.cacheQuery_of_ne _ _ (fun he => hne (congrArg Prod.fst he))

#print axioms strongBallotSimOracle_other_statement
#print axioms strongBallotSimOracle_unflagged_valid
#print axioms strongBallotSimOracle_cache_le
#print axioms strongBallotSimOracle_bad_probability
#print axioms strongBallotSimOracle_bad_probability_le

end ExplainableCrypto.Helios.Computational
