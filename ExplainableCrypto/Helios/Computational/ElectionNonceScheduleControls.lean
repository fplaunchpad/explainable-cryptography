import ExplainableCrypto.Helios.Computational.ElectionNonceSchedule
import ExplainableCrypto.Helios.Computational.ElectionOracleControls

/-! Independent coins and retained public answers are necessary for scheduling.
The finite controls use ZMod 11; they make no cryptographic hardness claim. -/
namespace ExplainableCrypto.Helios.Computational.ElectionNonceScheduleControls
open OracleComp OracleSpec ElectionOracle ElectionCache
open ElectionOracleControls (Scalar keyRequest populated)
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar

private theorem one_supported : (1 : Scalar) ∈ support (sampleNonzero Scalar) := by
  simp only [sampleNonzero,support_map]
  exact ⟨1,by simp,by simp⟩

private theorem two_supported : (2 : Scalar) ∈ support (sampleNonzero Scalar) := by
  simp only [sampleNonzero,support_map]
  exact ⟨Units.mk0 2 (by decide),by simp,rfl⟩

/-- The two historical nonzero nonce draws can produce different commitments. -/
theorem distinct_pair_supported :
    ((1,2) : Scalar × Scalar) ∈ support (drawNoncePair Scalar) := by
  simp only [drawNoncePair,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff]
  exact ⟨1,one_supported,2,two_supported,rfl⟩

/-- Reusing one sampled nonce changes the law, despite equal marginal laws. -/
theorem shared_nonce_changes_law :
    𝒮[drawNoncePair Scalar] ≠ 𝒮[(fun r => (r,r)) <$> sampleNonzero Scalar] := by
  intro he
  have h := (mem_support_iff_of_evalSPMF_eq he (1,2)).mp distinct_pair_supported
  simp only [support_map,Set.mem_image] at h
  obtain ⟨r,_,hr⟩ := h
  have h1 := congrArg Prod.fst hr
  have h2 := congrArg Prod.snd hr
  exact (by decide : (1 : Scalar) ≠ 2) (h1.symm.trans h2)

/-- Independent private sampling does not discard an earlier public answer. -/
theorem old_answer_preserved :
    run (do let r ← liftProb (sampleNonzero Scalar)
            let c ← ask keyRequest
            pure (r,c)) populated =
      (fun r => ((r,5),populated)) <$> sampleNonzero Scalar := by
  rw [run_liftProb_bind]
  simp only [run_bind,run_ask,run_pure]
  simp [populated,QueryCache.cacheQuery,
    ElectionOracleControls.partialRequest,keyRequest]

/-- Resetting the cache instead produces a fresh uniform answer. -/
theorem reset_answer_probability :
    Pr[fun out => out.1 = (5 : Scalar) | run (ask keyRequest) ∅] = (11 : ENNReal)⁻¹ := by
  simp only [run_ask,QueryCache.empty_apply,bind_pure_comp,probEvent_map,Function.comp_def,
    probEvent_eq_eq_probOutput,probOutput_uniformSample]
  norm_num

/-- The retained cached answer has probability one, contradicting reset behavior. -/
theorem retained_answer_probability :
    Pr[fun out => out.1 = (5 : Scalar) | run (ask keyRequest) populated] = 1 := by
  simp [run_ask,populated,QueryCache.cacheQuery,ElectionOracleControls.partialRequest,keyRequest]

#print axioms distinct_pair_supported
#print axioms shared_nonce_changes_law
#print axioms old_answer_preserved
#print axioms reset_answer_probability
#print axioms retained_answer_probability
end ExplainableCrypto.Helios.Computational.ElectionNonceScheduleControls
