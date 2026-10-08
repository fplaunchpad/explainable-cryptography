import ExplainableCrypto.Helios.Computational.TrusteeReachableSimulation
import ExplainableCrypto.Helios.Computational.HonestPrefixRejection
import ExplainableCrypto.Helios.Computational.ElectionNonceSchedule

/-! Compose the existing key and honest-pair simulators in the actual full
prefix. The full cache and fingerprint are part of the compared output. -/
namespace ExplainableCrypto.Helios.Computational.ElectionPrefixSimulation
open OracleComp OracleSpec ElectionOracle ElectionCache ElectionCacheBudget TrusteeReachableSimulation
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev Cast (F G : Type) := (Decision × Decision) × List (BoardEntry F G)

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem projected_cover (cache : Cache F G) (k : Nat) (hc : Covered cache k) :
    BallotCacheBound (project cache) k := by
  classical
  obtain ⟨Q,hQ,hcov⟩ := hc
  let tag := fun x : BallotStatement G × BallotCommitment G => Key.ballot x.1 x.2
  have ht : Function.Injective tag := by
    rintro ⟨s,c⟩ ⟨t,d⟩ h; cases h; rfl
  refine ⟨Q.preimage tag ht.injOn,?_,?_⟩
  · rw [Finset.card_preimage]
    exact (Finset.card_filter_le _ _).trans hQ
  · intro x hx
    exact Finset.mem_preimage.mpr (hcov _ hx)

omit [Fintype F] [DecidableEq F] in
private theorem key_project (g pk : G) (cache : Cache F G)
    (out : (SchnorrProof F G × Bool) × Cache F G)
    (ho : out ∈ support ((keySim (F := F) g pk).run cache)) : project out.2 = project cache := by
  simp only [keySim,TrusteeOracleSimulation.sim,StateT.run,support_map] at ho
  obtain ⟨t,_,rfl⟩ := ho
  unfold TrusteeOracleSimulation.finish
  cases cache (Key.key g pk t.1)
  · funext x
    simp [project,QueryCache.cacheQuery]
  · rfl

def restore {A : Type} (cache : Cache F G) (out : A × BallotProofOracleState F G) :
    (A × Bool) × Cache F G := ((out.1,out.2.2),replace cache out.2.1)

noncomputable def ballotsReal (g pk : G) (vote : Bool) (bad : Bool) (cache : Cache F G) :=
  restore cache <$> runBallotProofReal g pk (repairedCastHonestPairOracle g pk vote) (project cache,bad)

noncomputable def ballotsSim (g pk : G) (vote : Bool) (bad : Bool) (cache : Cache F G) :=
  restore cache <$> runBallotProofSim g pk (repairedCastHonestPairOracle g pk vote) (project cache,bad)

private theorem ballots_real_eq (g pk : G) (vote bad : Bool) (cache : Cache F G) :
    𝒮[ballotsReal g pk vote bad cache] =
      𝒮[do let coins ← drawHonestPair F
           let out ← run (liftBallot
             (repairedCastHonestPairWithCoinsOracle g pk vote coins.1 coins.2)) cache
           pure ((out.1,bad),out.2)] := by
  have h := evalSPMF_map_eq_of_evalSPMF_eq
    (repairedCastHonestPairOracle_real_eq g pk vote (project cache,bad)) (restore cache)
  simpa only [ballotsReal,liftBallot_run,map_bind,map_pure,bind_map_left,restore] using h

private theorem ballots_distance_le (g pk : G)
    (hg : Function.Injective (fun r : F => r • g)) (vote bad : Bool)
    (cache : Cache F G) (k : Nat) (hc : BallotCacheBound (project cache) k) :
    tvDist (ballotsReal g pk vote bad cache) (ballotsSim g pk vote bad cache) ≤
      6 * (15+(k : ℝ)) / (Fintype.card F : ℝ) := by
  exact (tvDist_map_le (restore cache) _ _).trans
    (repairedCastHonestPairOracle_simulation_le g pk hg vote (project cache,bad) k hc)

def publication (fingerprint : PublicParameters F G → Nat) (g pk : G)
    (keyProof : SchnorrProof F G) (cast : Cast F G) : PublicPrefix F G :=
  let parameters : PublicParameters F G := ⟨g,pk,keyProof,[0,1],[0,1,2]⟩
  ⟨parameters,fingerprint parameters,cast.1,cast.2⟩

private noncomputable def afterReal (fingerprint : PublicParameters F G → Nat) (g pk : G)
    (vote : Bool) (key : (SchnorrProof F G × Bool) × Cache F G) :=
  (fun out => ((publication fingerprint g pk key.1.1 out.1.1,out.1.2),out.2)) <$>
    ballotsReal g pk vote key.1.2 key.2

private noncomputable def afterSim (fingerprint : PublicParameters F G → Nat) (g pk : G)
    (vote : Bool) (key : (SchnorrProof F G × Bool) × Cache F G) :=
  (fun out => ((publication fingerprint g pk key.1.1 out.1.1,out.1.2),out.2)) <$>
    ballotsSim g pk vote key.1.2 key.2

noncomputable def real (fingerprint : PublicParameters F G → Nat) (g : G)
    (secret : F) (vote : Bool) (cache : Cache F G) :=
  (TrusteeOracleSimulation.real g secret (Key.key g (secret • g))).run cache >>=
    afterReal fingerprint g (secret • g) vote

/-- The simulator takes the public key and vote, with no secret-key argument.
It reuses the existing honest-pair simulation and both original submissions. -/
noncomputable def sim (fingerprint : PublicParameters F G → Nat) (g pk : G)
    (vote : Bool) (cache : Cache F G) :=
  (keySim (F := F) g pk).run cache >>= afterSim fingerprint g pk vote

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [AddCommGroup G] [Module F G] in
private theorem replace_covered (cache : Cache F G) (ballot : BallotOracleCache F G)
    (k b : Nat) (hc : Covered cache k) (hb : BallotCacheBound ballot b) :
    Covered (replace cache ballot) (k+b) := by
  obtain ⟨Q,hQ,hcov⟩ := hc
  obtain ⟨B,hB,hballot⟩ := hb
  let tag := fun x : BallotStatement G × BallotCommitment G => Key.ballot x.1 x.2
  refine ⟨Q ∪ B.image tag,?_,?_⟩
  · exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add hQ ((Finset.card_image_le).trans hB))
  · intro key hk
    cases key with
    | ballot s c => exact Finset.mem_union_right _ (Finset.mem_image_of_mem tag (hballot _ hk))
    | key g pk c => exact Finset.mem_union_left _ (hcov _ hk)
    | decryption g pk ct share c => exact Finset.mem_union_left _ (hcov _ hk)

omit [Fintype F] [DecidableEq F] in
private theorem key_covered (g pk : G) (cache : Cache F G) (k : Nat) (hc : Covered cache k)
    (out : (SchnorrProof F G × Bool) × Cache F G)
    (ho : out ∈ support ((keySim (F := F) g pk).run cache)) : Covered out.2 (k+1) := by
  simp only [keySim,TrusteeOracleSimulation.sim,StateT.run,support_map] at ho
  obtain ⟨t,_,rfl⟩ := ho
  unfold TrusteeOracleSimulation.finish
  cases cache (Key.key g pk t.1)
  · exact hc.cacheQuery _ _
  · exact hc.mono (Nat.le_succ k)

/-- The actual simulated prefix derives its full successor cover. The bound
uses a conservative union, retaining all key and decryption contexts. -/
theorem sim_covered (fingerprint : PublicParameters F G → Nat) (g pk : G)
    (vote : Bool) (cache : Cache F G) (k : Nat) (hc : Covered cache k)
    (out : (PublicPrefix F G × Bool) × Cache F G)
    (ho : out ∈ support (sim fingerprint g pk vote cache)) : Covered out.2 (2*k+13) := by
  simp only [sim,support_bind,Set.mem_iUnion] at ho
  obtain ⟨key,hkey,ho⟩ := ho
  have hk := key_covered g pk cache k hc key hkey
  have hp : BallotCacheBound (project key.2) k := by
    rw [key_project g pk cache key hkey]
    exact projected_cover cache k hc
  simp only [afterSim,ballotsSim,support_map] at ho
  obtain ⟨restored,⟨ballots,hballots,rfl⟩,rfl⟩ := ho
  have hb := runBallotProofSim_cache_bound g pk _ 12 k
    (repairedCastHonestPairOracle_query_bounds g pk vote).1 (project key.2,key.1.2) hp ballots hballots
  have h := replace_covered key.2 ballots.2.1 (k+1) (k+12) hk hb
  simpa only [restore,show k+1+(k+12)=2*k+13 by omega] using h

/-- The public parameter relation needed by finishing is derived on every
supported simulated prefix, including branches where an honest ballot rejects. -/
theorem sim_parameters (fingerprint : PublicParameters F G → Nat) (g pk : G)
    (vote : Bool) (cache : Cache F G) (out : (PublicPrefix F G × Bool) × Cache F G)
    (ho : out ∈ support (sim fingerprint g pk vote cache)) :
    out.1.1.parameters.generator = g ∧ out.1.1.parameters.publicKey = pk := by
  simp only [sim,support_bind,Set.mem_iUnion,afterSim,support_map] at ho
  obtain ⟨key,_,ballots,_,rfl⟩ := ho
  exact ⟨rfl,rfl⟩

private theorem composed_distance_le (fingerprint : PublicParameters F G → Nat)
    (g : G) (secret : F) (hg : Function.Injective (fun r : F => r • g)) (vote : Bool)
    (cache : Cache F G) (k : Nat) (hc : Covered cache k) :
    tvDist (real fingerprint g secret vote cache) (sim fingerprint g (secret • g) vote cache) ≤
      (7*(k : ℝ)+91) / (Fintype.card F : ℝ) := by
  obtain ⟨Q,hQ,hcov⟩ := hc
  have htag : Function.Injective (Key.key g (secret • g)) := by
    intro x y h; cases h; rfl
  have hkey : tvDist ((TrusteeOracleSimulation.real g secret (Key.key g (secret • g))).run cache)
      ((keySim g (secret • g)).run cache) ≤ (1+(k : ℝ)) * (Fintype.card F : ℝ)⁻¹ :=
    (TrusteeOracleSimulation.distance_le g secret _ htag hg cache Q hcov).trans (by gcongr)
  have hfirst := (tvDist_bind_right_le (afterReal fingerprint g (secret • g) vote) _ _).trans hkey
  have hsecond : tvDist ((keySim g (secret • g)).run cache >>= afterReal fingerprint g (secret • g) vote)
      ((keySim g (secret • g)).run cache >>= afterSim fingerprint g (secret • g) vote) ≤
        6*(15+(k : ℝ)) / (Fintype.card F : ℝ) := by
    apply tvDist_bind_left_le_const
    intro key hk
    have hp : BallotCacheBound (project key.2) k := by
      rw [key_project g (secret • g) cache key hk]
      exact projected_cover cache k ⟨Q,hQ,hcov⟩
    exact (tvDist_map_le _ _ _).trans (ballots_distance_le g (secret • g) hg vote key.1.2 key.2 k hp)
  exact (tvDist_triangle _ _ _).trans ((add_le_add hfirst hsecond).trans_eq (by rw [div_eq_mul_inv]; ring))

/-- This is the actual fixed-secret prefix subcomputation of the scheduled
world: original honest coins, historical key nonce and original prefix body. -/
noncomputable def source (fingerprint : PublicParameters F G → Nat) (g : G)
    (secret : F) (vote : Bool) : Comp F G (PublicPrefix F G) := do
  let coins ← liftProb (drawHonestPair F)
  let keyNonce ← liftProb (sampleNonzero F)
  prefixWithCoins fingerprint g secret keyNonce vote coins.1 coins.2

/-- The composed real runner has the actual original prefix distribution,
including fingerprint, decisions, retained board, full cache and flag false. -/
theorem real_eq (fingerprint : PublicParameters F G → Nat) (g : G)
    (secret : F) (vote : Bool) (cache : Cache F G) :
    𝒮[(fun out => ((out.1,false),out.2)) <$> run (source fingerprint g secret vote) cache] =
      𝒮[real fingerprint g secret vote cache] := by
  unfold real
  rw [TrusteeOracleSimulation.key_real,bind_map_left]
  simp only [source,prefixWithCoins,run_bind,run_pure,run_liftProb,bind_map_left,
    map_bind,map_pure,bind_assoc]
  conv_lhs => rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr'
  intro keyNonce
  conv_lhs => rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr'
  intro key
  have h := evalSPMF_map_eq_of_evalSPMF_eq (ballots_real_eq g (secret • g) vote false key.2)
    (fun out => ((publication fingerprint g (secret • g) key.1 out.1.1,out.1.2),out.2))
  simpa only [afterReal,map_bind,map_pure,publication] using h.symm

/-- Actual prefix simulation in the full cache. Existing honest-pair bounds
supply the six proof requests; the key proof does not enlarge the ballot cache. -/
theorem prefix_distance_le (fingerprint : PublicParameters F G → Nat) (g : G)
    (secret : F) (hg : Function.Injective (fun r : F => r • g)) (vote : Bool)
    (cache : Cache F G) (k : Nat) (hc : Covered cache k) :
    tvDist ((fun out => ((out.1,false),out.2)) <$> run (source fingerprint g secret vote) cache)
      (sim fingerprint g (secret • g) vote cache) ≤
        (7*(k : ℝ)+91) / (Fintype.card F : ℝ) := by
  have h := composed_distance_le fingerprint g secret hg vote cache k hc
  unfold tvDist at h ⊢
  rw [real_eq]
  exact h

/-- The initial cache condition is derived after arbitrary bounded prior
full-election queries; the original full prefix observations are retained. -/
theorem prefix_after_queries_le {A : Type} (prior : Comp F G A) (n : Nat)
    (hb : prior.IsQueryBoundP (isHash (F := F)) n) (out : A × Cache F G)
    (ho : out ∈ support (run prior ∅)) (fingerprint : PublicParameters F G → Nat)
    (g : G) (secret : F) (hg : Function.Injective (fun r : F => r • g)) (vote : Bool) :
    tvDist ((fun result => ((result.1,false),result.2)) <$>
      run (source fingerprint g secret vote) out.2)
      (sim fingerprint g (secret • g) vote out.2) ≤
        (7*(n : ℝ)+91) / (Fintype.card F : ℝ) := by
  apply prefix_distance_le fingerprint g secret hg vote out.2 n
  simpa using run_covered prior n 0 hb ∅ Covered.empty out ho

omit [SampleableType F] in
/-- Exact source factoring identifies the prefix used by the actual scheduled
world, without replacing any attacker action or trustee publication. -/
theorem world_source {State : Type} (fingerprint : PublicParameters F G → Nat) (g : G)
    (adversary : Adversary F G State) (vote : Bool) :
    ElectionNonceSchedule.world fingerprint g adversary vote = (do
      let secret ← liftProb (sampleNonzero F)
      let before ← source fingerprint g secret vote
      let (submission,saved) ← adversary.castBallot before
      let view ← ElectionNonceSchedule.finish secret before submission
      let guess ← adversary.guessVote saved view
      pure (view,guess)) := by
  simp only [ElectionNonceSchedule.world,source,bind_assoc]

/-- Only the actual public prefix reaches later code; the sticky flag stays
private. Both prefix and later result remain in the statistical comparison. -/
def follow {A : Type} (next : PublicPrefix F G → Comp F G A)
    (out : (PublicPrefix F G × Bool) × Cache F G) :
    ProbComp (((PublicPrefix F G × A) × Bool) × Cache F G) :=
  (fun tail => (((out.1.1,tail.1),out.1.2),tail.2)) <$> run (next out.1.1) out.2

/-- Arbitrary later full-oracle queries preserve the reachable-prefix bound.
No bound or purity assumption is imposed on the continuation. -/
theorem continuation_after_queries_le {A B : Type} (prior : Comp F G A) (n : Nat)
    (hb : prior.IsQueryBoundP (isHash (F := F)) n) (out : A × Cache F G)
    (ho : out ∈ support (run prior ∅)) (fingerprint : PublicParameters F G → Nat)
    (g : G) (secret : F) (hg : Function.Injective (fun r : F => r • g)) (vote : Bool)
    (next : PublicPrefix F G → Comp F G B) :
    tvDist ((fun result => ((result.1,false),result.2)) <$> run
      (do let before ← source fingerprint g secret vote
          let tail ← next before
          pure (before,tail)) out.2)
      (sim fingerprint g (secret • g) vote out.2 >>= follow next) ≤
        (7*(n : ℝ)+91) / (Fintype.card F : ℝ) := by
  have h := (tvDist_bind_right_le (follow next) _ _).trans
    (prefix_after_queries_le prior n hb out ho fingerprint g secret hg vote)
  simpa only [follow,map_eq_bind_pure_comp,Function.comp_def,bind_assoc,pure_bind,
    run_bind,run_pure] using h

#print axioms real_eq
#print axioms prefix_distance_le
#print axioms prefix_after_queries_le
#print axioms world_source
#print axioms continuation_after_queries_le
#print axioms sim_covered
#print axioms sim_parameters
end ExplainableCrypto.Helios.Computational.ElectionPrefixSimulation
