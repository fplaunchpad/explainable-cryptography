import ExplainableCrypto.Helios.Computational.TrusteeSimulation
import ExplainableCrypto.Helios.Computational.ElectionCache

/-! Witness-free trustee proof programming in the actual full election cache.
Key and decryption contexts are concrete instances of this one Schnorr step.
A prior answer is preserved and flagged, including when it agrees. -/
namespace ExplainableCrypto.Helios.Computational.TrusteeOracleSimulation
open OracleComp OracleSpec ElectionOracle
variable {F G H : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup H] [Module F H] [DecidableEq G]

def withCoins (base : H) (secret : F) (tag : H → Key G) (nonce : F) :
    Comp F G (SchnorrProof F H) := do
  let c ← ask (tag (nonce • base))
  pure ⟨nonce • base,nonce+c*secret⟩

noncomputable def real (base : H) (secret : F) (tag : H → Key G) :
    StateT (Cache F G) ProbComp (SchnorrProof F H × Bool) := fun cache => do
  let r ← sampleNonzero F
  let out ← run (withCoins base secret tag r) cache
  pure ((out.1,false),out.2)

def finish (tag : H → Key G) (cache : Cache F G) (t : H × F × F) :
    (SchnorrProof F H × Bool) × Cache F G :=
  let p : SchnorrProof F H := ⟨t.1,t.2.2⟩
  match cache (tag t.1) with
  | some _ => ((p,true),cache)
  | none => ((p,false),cache.cacheQuery (tag t.1) t.2.1)

def sim (base key : H) (tag : H → Key G) :
    StateT (Cache F G) ProbComp (SchnorrProof F H × Bool) := fun cache =>
  finish tag cache <$> TrusteeSimulation.transcript base key

private def realNext (base : H) (secret : F) (tag : H → Key G) (cache : Cache F G) (r : F) :=
  (fun out => ((out.1,false),out.2)) <$> run (withCoins base secret tag r) cache

private def simNext (base : H) (secret : F) (tag : H → Key G) (cache : Cache F G) (r : F) := do
  let c ← uniformSample F
  pure (finish tag cache (r • base,c,r+c*secret))

omit [Fintype F] [DecidableEq F] in
private theorem off_cache (base : H) (secret : F) (tag : H → Key G)
    (cache : Cache F G) (r : F) (hfresh : ¬ (cache (tag (r • base))).isSome = true) :
    𝒮[realNext base secret tag cache r] = 𝒮[simNext base secret tag cache r] := by
  have hc : cache (tag (r • base)) = none := by
    cases h : cache (tag (r • base)) <;> simp_all
  apply congrArg evalSPMF
  simp only [realNext,withCoins,run_bind,run_pure,run_ask,hc]
  simp [simNext,finish,hc]

private theorem full_to_sim (base : H) (secret : F) (tag : H → Key G) (cache : Cache F G) :
    𝒮[uniformSample F >>= simNext base secret tag cache] =
      𝒮[(sim base (secret • base) tag).run cache] := by
  have h := evalSPMF_map_eq_of_evalSPMF_eq (TrusteeSimulation.full_eq base secret) (finish tag cache)
  simpa [sim,simNext,StateT.run,map_bind,bind_pure_comp] using h

omit [DecidableEq G] in
private theorem full_bad_eq (base : H) (secret : F) (tag : H → Key G) (cache : Cache F G) :
    Pr[fun r : F => (cache (tag (r • base))).isSome = true | uniformSample F] =
      Pr[fun t => (cache (tag t.1)).isSome = true | TrusteeSimulation.transcript (F := F) base (secret • base)] := by
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (TrusteeSimulation.full_eq base secret).symm]
  rw [probEvent_bind_eq_tsum,probEvent_eq_tsum_ite]
  apply tsum_congr
  intro r
  rw [probEvent_bind_of_const (uniformSample F)
    (r := if (cache (tag (r • base))).isSome = true then 1 else 0)
    (by intro c _; simp)]
  simp

omit [DecidableEq F] in
/-- A finite prior query domain bounds simulated commitment collisions. The
statement-to-key tag is injective; both actual trustee tags discharge this. -/
theorem collision_le (base key : H) (tag : H → Key G) (htag : Function.Injective tag)
    (hg : Function.Injective (fun r : F => r • base)) (queries : Finset (Key G)) :
    Pr[fun t => tag t.1 ∈ queries | TrusteeSimulation.transcript (F := F) base key] ≤
      queries.card * (Fintype.card F : ENNReal)⁻¹ := by
  classical
  induction queries using Finset.induction_on with
  | empty => simp
  | @insert k queries hk ih =>
    simp only [Finset.mem_insert]
    have hb : Pr[fun t => tag t.1 = k | TrusteeSimulation.transcript (F := F) base key] ≤
        (Fintype.card F : ENNReal)⁻¹ := by
      by_cases he : ∃ c, tag c = k
      · obtain ⟨c,rfl⟩ := he
        simpa only [htag.eq_iff] using TrusteeSimulation.commitment_probability_le base key c hg
      · have hn : ∀ c, tag c ≠ k := by simpa using he
        simp [hn]
    calc
      _ ≤ Pr[fun t => tag t.1 = k | TrusteeSimulation.transcript (F := F) base key] +
          Pr[fun t => tag t.1 ∈ queries | TrusteeSimulation.transcript (F := F) base key] :=
        probEvent_or_le _ _ _
      _ ≤ (Fintype.card F : ENNReal)⁻¹ + queries.card * (Fintype.card F : ENNReal)⁻¹ :=
        add_le_add hb ih
      _ = _ := by rw [Finset.card_insert_of_notMem hk]; push_cast; ring

/-- Compare the historical nonzero-nonce step and witness-free programming,
including the complete original cache, returned proof and collision flag. -/
theorem distance_le (base : H) (secret : F) (tag : H → Key G) (htag : Function.Injective tag)
    (hg : Function.Injective (fun r : F => r • base)) (cache : Cache F G)
    (queries : Finset (Key G)) (hcover : ∀ k, (cache k).isSome = true → k ∈ queries) :
    tvDist ((real base secret tag).run cache) ((sim base (secret • base) tag).run cache) ≤
      (1 + (queries.card : ℝ)) * (Fintype.card F : ℝ)⁻¹ := by
  have hn := (tvDist_bind_right_le (realNext base secret tag cache)
    (sampleNonzero F) (uniformSample F)).trans sampleNonzero_uniform_tv_le
  have hb := tvDist_bind_left_event_le (uniformSample F)
    (realNext base secret tag cache) (simNext base secret tag cache)
    (fun r => (cache (tag (r • base))).isSome = true) (off_cache base secret tag cache)
  rw [full_bad_eq base secret tag cache] at hb
  have hp := (probEvent_mono (fun t _ ht => hcover (tag t.1) ht)).trans
    (collision_le base (secret • base) tag htag hg queries)
  have hq : (Fintype.card F : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := F)
  have hfinite : (queries.card : ENNReal) * (Fintype.card F : ENNReal)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.inv_ne_top.mpr hq)
  have hpr := ENNReal.toReal_mono hfinite hp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_natCast] at hpr
  have hs : tvDist (uniformSample F >>= realNext base secret tag cache)
      ((sim base (secret • base) tag).run cache) ≤
        (queries.card : ℝ) * (Fintype.card F : ℝ)⁻¹ := by
    unfold tvDist at hb ⊢
    rw [full_to_sim base secret tag cache] at hb
    exact hb.trans hpr
  have he : (real base secret tag).run cache = sampleNonzero F >>= realNext base secret tag cache := by
    unfold real StateT.run
    apply bind_congr
    intro r
    simp [realNext]
  rw [he]
  exact (tvDist_triangle _ _ _).trans ((add_le_add hn hs).trans_eq (by ring))

omit [Fintype F] [DecidableEq F] in
/-- Existing answers survive even a flagged simulation attempt. -/
theorem sim_cache_le (base key : H) (tag : H → Key G) (cache : Cache F G)
    (out : (SchnorrProof F H × Bool) × Cache F G)
    (ho : out ∈ support ((sim base key tag).run cache)) : cache ≤ out.2 := by
  simp only [sim,StateT.run,support_map] at ho
  obtain ⟨t,_,rfl⟩ := ho
  unfold finish
  cases hc : cache (tag t.1)
  · exact QueryCache.le_cacheQuery cache hc
  · exact le_rfl

omit [Fintype F] [DecidableEq F] in
/-- An unflagged simulated proof verifies under its actual final cached answer. -/
theorem sim_valid (base key : H) (tag : H → Key G) (cache : Cache F G)
    (out : (SchnorrProof F H × Bool) × Cache F G)
    (ho : out ∈ support ((sim base key tag).run cache)) (hbad : out.1.2 = false) :
    ∃ c, out.2 (tag out.1.1.commitment) = some c ∧ out.1.1.Valid (fun _ => c) base key := by
  simp only [sim,StateT.run,support_map] at ho
  obtain ⟨t,ht,rfl⟩ := ho
  simp only [TrusteeSimulation.transcript,Schnorr.simTranscript,support_bind,
    support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at ht
  obtain ⟨c,_,z,_,rfl⟩ := ht
  cases hc : cache (tag (z • base - c • key)) with
  | some answer => simp [finish,hc] at hbad
  | none =>
    refine ⟨c,?_,?_⟩
    · dsimp only [finish]
      rw [hc]
      simp
    · simpa [finish,hc,TrusteeSimulation.proof] using TrusteeSimulation.proof_valid base key c z

variable [AddCommGroup G] [Module F G]

omit [DecidableEq F] in
/-- The generic real key step is the original full-context algorithm. -/
theorem key_real (g : G) (secret : F) (cache : Cache F G) :
    (real g secret (Key.key g (secret • g))).run cache =
      (fun out => ((out.1,false),out.2)) <$>
        run (do let r ← liftProb (sampleNonzero F); keyWithCoins g secret r) cache := by
  rw [ElectionCache.run_liftProb_bind]
  simp [real,withCoins,keyWithCoins,StateT.run,map_bind]

omit [DecidableEq F] in
/-- The generic real equality-of-logs step is the original decryption proof,
with ciphertext, share and both commitments retained in the query context. -/
theorem partial_real (g : G) (secret : F) (ct : Ciphertext G) (cache : Cache F G) :
    (real (g,ct.1) secret (Key.decryption g (secret • g) ct (partialDecrypt secret ct))).run cache =
      (fun out => ((out.1,false),out.2)) <$>
        run (do let r ← liftProb (sampleNonzero F); partialWithCoins g secret r ct) cache := by
  rw [ElectionCache.run_liftProb_bind]
  simp [real,withCoins,partialWithCoins,StateT.run,map_bind]

#print axioms collision_le
#print axioms distance_le
#print axioms sim_cache_le
#print axioms sim_valid
#print axioms key_real
#print axioms partial_real
end ExplainableCrypto.Helios.Computational.TrusteeOracleSimulation
