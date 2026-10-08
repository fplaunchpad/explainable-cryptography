import ExplainableCrypto.Helios.Computational.StrongBallotProgrammingDistance

/-! Finite cache covers derived from supported adaptive oracle executions.
Only strong-hash queries consume the budget; uniform prover coins do not. -/
namespace ExplainableCrypto.Helios.Computational

open OracleComp OracleSpec
variable {F G : Type} [DecidableEq G] [SampleableType F]

def BallotCacheBound (cache : BallotOracleCache F G) (n : Nat) : Prop :=
  ∃ queries : Finset (BallotStatement G × BallotCommitment G),
    queries.card ≤ n ∧ ∀ key, (cache key).isSome = true → key ∈ queries

def isBallotHashQuery : (BallotOracleSpec F G).Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred (isBallotHashQuery (F := F) (G := G)) := fun key =>
  match key with
  | .inl _ => inferInstanceAs (Decidable False)
  | .inr _ => inferInstanceAs (Decidable True)

omit [DecidableEq G] [SampleableType F] in
theorem BallotCacheBound.mono {cache : BallotOracleCache F G} {n m : Nat}
    (h : BallotCacheBound cache n) (hn : n ≤ m) : BallotCacheBound cache m := by
  obtain ⟨Q,hQ,hcov⟩ := h
  exact ⟨Q,hQ.trans hn,hcov⟩

omit [DecidableEq G] [SampleableType F] in
theorem BallotCacheBound.empty : BallotCacheBound (∅ : BallotOracleCache F G) 0 := by
  exact ⟨∅,by simp,by simp⟩

omit [SampleableType F] in
theorem BallotCacheBound.cacheQuery {cache : BallotOracleCache F G} {n : Nat}
    (h : BallotCacheBound cache n) (key : BallotStatement G × BallotCommitment G) (c : F) :
    BallotCacheBound (cache.cacheQuery key c) (n+1) := by
  obtain ⟨Q,hQ,hcov⟩ := h
  refine ⟨insert key Q, (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hQ 1), ?_⟩
  intro key' hk
  by_cases he : key' = key
  · exact he ▸ Finset.mem_insert_self _ _
  · rw [QueryCache.cacheQuery_of_ne cache c he] at hk
    exact Finset.mem_insert_of_mem (hcov key' hk)

/-- The cover is derived for each reachable cache, including adaptive queries
whose next input depends on all previous answers. -/
theorem runBallotOracle_cache_bound {α : Type} (oa : BallotOracleComp F G α)
    (n k : Nat) (hb : oa.IsQueryBoundP (isBallotHashQuery (F := F)) n)
    (cache : BallotOracleCache F G) (hc : BallotCacheBound cache k)
    (out : α × BallotOracleCache F G) (ho : out ∈ support (runBallotOracle oa cache)) :
    BallotCacheBound out.2 (k+n) := by
  induction oa using OracleComp.inductionOn generalizing n k cache with
  | pure x =>
    simp only [runBallotOracle, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at ho
    subst out
    exact hc.mono (Nat.le_add_right _ _)
  | query_bind t next ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    simp only [runBallotOracle, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      support_bind, Set.mem_iUnion] at ho
    obtain ⟨answer,ha,ho⟩ := ho
    cases t with
    | inl u =>
      simp only [ballotRandomImpl, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply,
        StateT.run_monadLift, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at ha
      obtain ⟨v,_,rfl⟩ := ha
      exact ih v n k (by simpa [isBallotHashQuery] using hb.2 v) cache hc ho
    | inr key =>
      have hpos : 0 < n := by simpa [isBallotHashQuery] using hb.1
      have hrest := hb.2
      simp only [ballotRandomImpl, QueryImpl.add_apply_inr, randomOracle.run_eq] at ha
      cases hkey : cache key with
      | some c =>
        simp only [hkey, support_pure, Set.mem_singleton_iff] at ha
        subst answer
        exact (ih c (n-1) k (by simpa [isBallotHashQuery] using hrest c) cache hc ho).mono
          (by omega)
      | none =>
        simp only [hkey, support_bind, support_pure, Set.mem_iUnion,
          Set.mem_singleton_iff] at ha
        obtain ⟨c,_,rfl⟩ := ha
        have h := ih c (n-1) (k+1) (by simpa [isBallotHashQuery] using hrest c)
          (cache.cacheQuery key c) (hc.cacheQuery key c) ho
        simpa [show k+1+(n-1)=k+n by omega] using h

variable [Field F] [AddCommGroup G] [Module F G]

theorem strongBallotSimOracle_cache_bound (stmt : BallotStatement G)
    (cache : BallotOracleCache F G) (k : Nat) (hc : BallotCacheBound cache k)
    (out : (Proof01 F G × Bool) × BallotOracleCache F G)
    (ho : out ∈ support ((strongBallotSimOracle (F := F) stmt).run cache)) :
    BallotCacheBound out.2 (k+1) := by
  simp only [strongBallotSimOracle, StateT.run, support_bind, Set.mem_iUnion] at ho
  obtain ⟨t,_,ho⟩ := ho
  cases hk : cache (stmt,t.1) with
  | some c =>
    simp only [hk, support_pure, Set.mem_singleton_iff] at ho
    subst out
    exact hc.mono (by omega)
  | none =>
    simp only [hk, support_pure, Set.mem_singleton_iff] at ho
    subst out
    exact hc.cacheQuery _ _

#print axioms runBallotOracle_cache_bound
#print axioms strongBallotSimOracle_cache_bound

variable [Fintype F] [DecidableEq F]

/-- Budget form used by adaptive composition; a cover is extracted from the
proved cache invariant rather than supplied as a separate list of keys. -/
theorem strongBallot_programming_step_of_cache_bound (stmt : BallotStatement G)
    (wit : BallotWitness F) (hw : stmt.Witnesses wit)
    (hg : Function.Injective (fun r : F => r • stmt.generator))
    (cache : BallotOracleCache F G) (k : Nat) (hc : BallotCacheBound cache k) :
    tvDist ((strongBallotRealOracle stmt wit).run cache)
      ((strongBallotSimOracle (F := F) stmt).run cache) ≤
        3 * (Fintype.card F : ℝ)⁻¹ + (k : ℝ) * (Fintype.card F : ℝ)⁻¹ := by
  obtain ⟨Q,hQ,hcov⟩ := hc
  apply (strongBallot_programming_step_distance_le stmt wit hw hg cache Q hcov).trans
  gcongr

/-- The initial-cover premise of the one-step theorem is discharged after any
query-bounded adaptive execution starting from the empty cache. -/
theorem strongBallot_programming_after_queries_le {α : Type} (oa : BallotOracleComp F G α)
    (n : Nat) (hb : oa.IsQueryBoundP (isBallotHashQuery (F := F)) n)
    (out : α × BallotOracleCache F G) (ho : out ∈ support (runBallotOracle oa ∅))
    (stmt : BallotStatement G) (wit : BallotWitness F) (hw : stmt.Witnesses wit)
    (hg : Function.Injective (fun r : F => r • stmt.generator)) :
    tvDist ((strongBallotRealOracle stmt wit).run out.2)
      ((strongBallotSimOracle (F := F) stmt).run out.2) ≤
        3 * (Fintype.card F : ℝ)⁻¹ + (n : ℝ) * (Fintype.card F : ℝ)⁻¹ := by
  exact strongBallot_programming_step_of_cache_bound stmt wit hw hg out.2 n
    (by simpa using runBallotOracle_cache_bound oa n 0 hb ∅ BallotCacheBound.empty out ho)

#print axioms strongBallot_programming_step_of_cache_bound
#print axioms strongBallot_programming_after_queries_le

end ExplainableCrypto.Helios.Computational
