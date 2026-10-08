import ExplainableCrypto.Helios.Computational.ElectionOracle
import ExplainableCrypto.Helios.Computational.HonestPrefixRejection

/-! The actual ballot runtime inside an arbitrary full election cache.
Projection/reconstruction preserve prior queries and the other proof domains. -/
namespace ExplainableCrypto.Helios.Computational.ElectionCache
open OracleComp OracleSpec ElectionOracle

def project {F G : Type} (cache : Cache F G) : BallotOracleCache F G :=
  fun k => cache (.ballot k.1 k.2)

def replace {F G : Type} (cache : Cache F G) (ballot : BallotOracleCache F G) : Cache F G :=
  fun k => match k with
    | .ballot s c => ballot (s,c)
    | .key g pk c => cache (.key g pk c)
    | .decryption g pk ct share c => cache (.decryption g pk ct share c)

theorem project_replace {F G : Type} (cache : Cache F G) (ballot : BallotOracleCache F G) :
    project (replace cache ballot) = ballot := by rfl

theorem replace_project {F G : Type} (cache : Cache F G) :
    replace cache (project cache) = cache := by
  funext k; cases k <;> rfl

theorem replace_replace {F G : Type} (cache : Cache F G) (a b : BallotOracleCache F G) :
    replace (replace cache a) b = replace cache b := by
  funext k; cases k <;> rfl

theorem replace_update {F G : Type} [DecidableEq G] (cache : Cache F G)
    (ballot : BallotOracleCache F G) (s : BallotStatement G) (c : BallotCommitment G) (a : F) :
    replace cache (ballot.cacheQuery (s,c) a) = (replace cache ballot).cacheQuery (.ballot s c) a := by
  funext k
  cases k with
  | ballot t d =>
    by_cases h : (t,d) = (s,c)
    · cases h
      simp [replace]
    · have hn : Key.ballot t d ≠ Key.ballot s c := by
        intro he
        cases he
        exact h rfl
      simp only [replace,QueryCache.cacheQuery_of_ne _ _ h,
        QueryCache.cacheQuery_of_ne _ _ hn]
  | key g pk d => simp [replace,QueryCache.cacheQuery]
  | decryption g pk ct share d => simp [replace,QueryCache.cacheQuery]

variable {F G : Type} [DecidableEq G] [SampleableType F]

private theorem ballot_pure {A : Type} (a : A) (cache : BallotOracleCache F G) :
    runBallotOracle (pure a) cache = pure (a,cache) := by simp [runBallotOracle]

private theorem query_eq (t : (BallotOracleSpec F G).Domain) (cache : Cache F G) :
    run (ballotImpl F G t) cache =
      (fun out => (out.1,replace cache out.2)) <$>
        runBallotOracle (liftM ((BallotOracleSpec F G).query t)) (project cache) := by
  cases t with
  | inl n =>
    simp [ballotImpl,run,runBallotOracle,randomImpl,ballotRandomImpl,replace_project]
  | inr k =>
    change run (ask (.ballot k.1 k.2)) cache =
      (fun out => (out.1,replace cache out.2)) <$>
        runBallotOracle (ballotChallengeOracle k.1 k.2) (project cache)
    rw [run_ask,runBallotOracle_query]
    cases h : cache (.ballot k.1 k.2) <;>
      simp [project,h,replace_update,replace_project]

/-- All source query trees and results agree, with the full final cache
reconstructed. No freshness, empty-cache or frame premise is supplied. -/
theorem liftBallot_run {A : Type} (oa : BallotOracleComp F G A) (cache : Cache F G) :
    run (liftBallot oa) cache =
      (fun out => (out.1,replace cache out.2)) <$> runBallotOracle oa (project cache) := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure a => simp [liftBallot,run_pure,ballot_pure,replace_project]
  | query_bind t next ih =>
    simp only [liftBallot,simulateQ_bind,simulateQ_spec_query,run_bind,query_eq,
      runBallotOracle_bind,bind_map_left,map_bind]
    apply bind_congr
    intro out
    simpa only [liftBallot,project_replace,replace_replace,Functor.map_map,Function.comp_def]
      using ih out.1 (replace cache out.2)

theorem run_liftProb_bind {A B : Type} (oa : ProbComp A) (next : A → Comp F G B)
    (cache : Cache F G) :
    run (do let a ← liftProb oa; next a) cache =
      (do let a ← oa; run (next a) cache) := by
  have hl : simulateQ (randomImpl (F := F) (G := G)) (liftProb oa) =
      (monadLift oa : StateT (Cache F G) ProbComp A) := by
    rw [liftProb,randomImpl,QueryImpl.simulateQ_add_liftComp_left]
    change simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (Cache F G) ProbComp)) oa = _
    rw [simulateQ_liftTarget,simulateQ_ofLift_eq_self]
  simp only [run,simulateQ_bind,hl,StateT.run_bind,StateT.run_monadLift,
    monad_norm,monadLift_self]

/-- Private probability sampling preserves the complete initial election cache. -/
theorem run_liftProb {A : Type} (oa : ProbComp A) (cache : Cache F G) :
    run (liftProb oa) cache = (fun a => (a,cache)) <$> oa := by
  have h := run_liftProb_bind oa (fun a => (pure a : Comp F G A)) cache
  simpa only [bind_pure,run_pure,bind_pure_comp] using h

private theorem run_map {A B : Type} (f : A → B) (oa : Comp F G A) (cache : Cache F G) :
    run (f <$> oa) cache = (fun out => (f out.1,out.2)) <$> run oa cache := by
  simp [run,simulateQ_map,StateT.run_map]

variable [Field F] [AddCommGroup G] [Module F G] [DecidableEq F]

/-- Honest acceptance is derived for the actual full prefix from arbitrary
prior queries. The key proof and fingerprint stay in the supported public record. -/
theorem prefix_accepts (fingerprint : PublicParameters F G → Nat) (g : G)
    (hg : Function.Injective (fun r : F => r • g)) (secret keyNonce : F) (vote : Bool)
    (alice bob : HonestCoins F) (hfree : ExpandedCollisionFree alice bob)
    (cache : Cache F G) (out : PublicPrefix F G × Cache F G)
    (ho : out ∈ support (run (prefixWithCoins fingerprint g secret keyNonce vote alice bob) cache)) :
    out.1.honestDecisions = (.accepted,.accepted) := by
  simp only [prefixWithCoins,run_bind,liftBallot_run,bind_map_left,run_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨key,hkey,cast,hcast,rfl⟩ := ho
  exact repairedCastHonestPairWithCoinsOracle_accepts_of_collisionFree
    g (secret • g) hg vote alice bob hfree (project key.2) cast hcast

/-- This is the honest-coin/prefix subcomputation of `ElectionOracle.world`.
The bound is uniform in the sampled secret/key nonce and all prior oracle state. -/
theorem prefix_rejection_le [Fintype F] (fingerprint : PublicParameters F G → Nat) (g : G)
    (hg : Function.Injective (fun r : F => r • g)) (secret keyNonce : F) (vote : Bool)
    (cache : Cache F G) :
    Pr[fun out => out.1.honestDecisions ≠ (.accepted,.accepted) |
      run (do let pair ← liftProb (drawHonestPair F)
              prefixWithCoins fingerprint g secret keyNonce vote pair.1 pair.2) cache] ≤
      9 * noncePointBound F := by
  classical
  rw [run_liftProb_bind]
  apply le_trans ?_ (drawHonestPair_expanded_collision_le (F := F))
  rw [probEvent_bind_eq_tsum,probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro pair
  by_cases hf : ExpandedCollisionFree pair.1 pair.2
  · simp only [hf,not_true_eq_false,ite_false]
    have hz : Pr[fun out => out.1.honestDecisions ≠ (.accepted,.accepted) |
        run (prefixWithCoins fingerprint g secret keyNonce vote pair.1 pair.2) cache] = 0 := by
      apply probEvent_eq_zero_iff.mpr
      intro out ho hn
      exact hn (prefix_accepts fingerprint g hg secret keyNonce vote pair.1 pair.2 hf cache out ho)
    simp only [hz,mul_zero,le_refl]
  · simp only [hf,not_false_eq_true,ite_true]
    exact mul_le_of_le_one_right' probEvent_le_one

variable [Fintype F]

/-- The actual challenger prefix, retaining the secret and decryption nonces
locally for the finish. `world_eq_samplePrefix` proves exact source factoring. -/
noncomputable def samplePrefix (fingerprint : PublicParameters F G → Nat) (g : G) (vote : Bool) :
    Comp F G (F × (F × F) × PublicPrefix F G) := do
  let secret ← liftProb (sampleNonzero F)
  let keyNonce ← liftProb (sampleNonzero F)
  let decryptionNonces ← liftProb (drawNoncePair F)
  let pair ← liftProb (drawHonestPair F)
  let before ← prefixWithCoins fingerprint g secret keyNonce vote pair.1 pair.2
  pure (secret,decryptionNonces,before)

omit [SampleableType F] in
theorem world_eq_samplePrefix {State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (adversary : Adversary F G State) (vote : Bool) :
    world fingerprint g adversary vote = (do
      let initial ← samplePrefix fingerprint g vote
      let (submission,saved) ← adversary.castBallot initial.2.2
      let view ← finishWithCoins initial.1 ![initial.2.1.1,initial.2.1.2] initial.2.2 submission
      adversary.guessVote saved view) := by
  simp only [world,samplePrefix,bind_assoc,pure_bind]

/-- The complete original prefix sampling inherits the bound uniformly in its
prior cache, without assuming honest acceptance or a pristine oracle. -/
theorem samplePrefix_rejection_le (fingerprint : PublicParameters F G → Nat) (g : G)
    (hg : Function.Injective (fun r : F => r • g)) (vote : Bool) (cache : Cache F G) :
    Pr[fun out => out.1.2.2.honestDecisions ≠ (.accepted,.accepted) |
      run (samplePrefix fingerprint g vote) cache] ≤ 9 * noncePointBound F := by
  simp only [samplePrefix,run_liftProb_bind]
  refine probEvent_bind_le_of_forall_le fun secret _ => ?_
  refine probEvent_bind_le_of_forall_le fun keyNonce _ => ?_
  refine probEvent_bind_le_of_forall_le fun decryptionNonces _ => ?_
  have h := prefix_rejection_le fingerprint g hg secret keyNonce vote cache
  rw [run_liftProb_bind] at h
  simpa only [run_bind,run_pure,bind_pure_comp,run_map,
    probEvent_bind_eq_tsum,probEvent_map,Function.comp_def] using h

theorem preparedPrefix_rejection_le {A : Type} (fingerprint : PublicParameters F G → Nat) (g : G)
    (hg : Function.Injective (fun r : F => r • g)) (vote : Bool)
    (prepare : Comp F G A) (cache : Cache F G) :
    Pr[fun out => out.1.2.2.honestDecisions ≠ (.accepted,.accepted) |
      run (do let _ ← prepare; samplePrefix fingerprint g vote) cache] ≤ 9 * noncePointBound F := by
  rw [run_bind]
  exact probEvent_bind_le_of_forall_le fun out _ =>
    samplePrefix_rejection_le fingerprint g hg vote out.2

#print axioms project_replace
#print axioms replace_project
#print axioms replace_replace
#print axioms replace_update
#print axioms liftBallot_run
#print axioms run_liftProb_bind
#print axioms run_liftProb
#print axioms prefix_accepts
#print axioms prefix_rejection_le
#print axioms world_eq_samplePrefix
#print axioms samplePrefix_rejection_le
#print axioms preparedPrefix_rejection_le
end ExplainableCrypto.Helios.Computational.ElectionCache
