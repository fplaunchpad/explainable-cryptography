import ExplainableCrypto.Helios.Computational.TrusteeReachableSimulation
import ExplainableCrypto.Helios.Computational.ElectionReplayControls

/-! Literal scalar fixtures complement the independent multiplicative p=23
script. No hardness assumption is made for the small control group. -/
namespace ExplainableCrypto.Helios.Computational.TrusteeSimulationControls
open OracleComp OracleSpec ElectionOracle TrusteeOracleSimulation
abbrev Scalar := ZMod 11
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar

/-- Nonce 4, challenge 5 and secret 3 give response 8 mod 11. -/
theorem literal_key :
    (TrusteeSimulation.proof (F := Scalar) (1 : Scalar) 3 5 8).commitment = 4 ∧
    (TrusteeSimulation.proof (F := Scalar) (1 : Scalar) 3 5 8).Valid (fun _ => 5) 1 3 := by
  exact ⟨by decide +kernel,TrusteeSimulation.proof_valid _ _ _ _⟩

/-- The equality-of-logs simulator reconstructs both commitments. -/
theorem literal_partial :
    (TrusteeSimulation.proof (F := Scalar) ((1,8) : Scalar × Scalar) (3,2) 5 8).commitment = (4,10) ∧
    (TrusteeSimulation.proof (F := Scalar) ((1,8) : Scalar × Scalar) (3,2) 5 8).Valid
      (fun _ => 5) (1,8) (3,2) := by
  exact ⟨by decide +kernel,TrusteeSimulation.proof_valid _ _ _ _⟩

theorem changed_challenge :
    ¬ (TrusteeSimulation.proof (F := Scalar) (1 : Scalar) 3 5 8).Valid (fun _ => 6) 1 3 := by
  unfold SchnorrProof.Valid TrusteeSimulation.proof
  decide +kernel

/-- Injectivity does not imply surjectivity onto the product group. -/
theorem product_not_surjective :
    ¬ Function.Surjective (fun r : Scalar => r • ((1,8) : Scalar × Scalar)) := by
  intro h
  obtain ⟨r,hr⟩ := h (0,1)
  have hz : r = 0 := by simpa using congrArg Prod.fst hr
  subst r
  have := congrArg Prod.snd hr
  norm_num at this

private noncomputable def historical : ProbComp (Scalar × Scalar × Scalar) := do
  let r ← sampleNonzero Scalar
  let c ← uniformSample Scalar
  pure (r,c,r+c*3)

/-- The simulator's zero commitment is possible, whereas historical nonzero
coins exclude it. Exact transcript simulation would therefore be false. -/
theorem nonzero_not_exact :
    𝒮[historical] ≠ 𝒮[TrusteeSimulation.transcript (F := Scalar) (1 : Scalar) 3] := by
  intro he
  have hs : (0,0,0) ∈ support (TrusteeSimulation.transcript (F := Scalar) (1 : Scalar) 3) := by
    simp only [TrusteeSimulation.transcript,Schnorr.simTranscript,support_bind,support_pure,
      Set.mem_iUnion,Set.mem_singleton_iff]
    exact ⟨0,by simp,0,by simp,by simp⟩
  have hr := (mem_support_iff_of_evalSPMF_eq he (0,0,0)).mpr hs
  simp only [historical,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at hr
  obtain ⟨r,hr,c,_,heq⟩ := hr
  exact sampleNonzero_ne_zero hr (congrArg Prod.fst heq).symm

def tag : Scalar → Key Scalar := Key.key 1 3

theorem fresh_programs :
    (finish tag (∅ : Cache Scalar Scalar) (4,5,8)).1.2 = false ∧
    (finish tag (∅ : Cache Scalar Scalar) (4,5,8)).2 (tag 4) = some 5 := by
  simp [finish]

/-- A cached answer is preserved and flagged even when it equals the new challenge. -/
theorem hit_preserves (answer : Scalar) :
    finish tag ((∅ : Cache Scalar Scalar).cacheQuery (tag 4) answer) (4,5,8) =
      ((⟨4,8⟩,true),(∅ : Cache Scalar Scalar).cacheQuery (tag 4) answer) := by
  simp [finish]

/-- Repeated hits are charged in the conservative structural prior-query bound. -/
theorem mixed_five_queries :
    ElectionReplayControls.mixed.IsQueryBoundP (ElectionCacheBudget.isHash (F := Scalar)) 5 := by
  simp [ElectionReplayControls.mixed,ask,isQueryBoundP_query_bind_iff,ElectionCacheBudget.isHash]

theorem mixed_four_insufficient :
    ¬ ElectionReplayControls.mixed.IsQueryBoundP (ElectionCacheBudget.isHash (F := Scalar)) 4 := by
  simp [ElectionReplayControls.mixed,ask,isQueryBoundP_query_bind_iff,ElectionCacheBudget.isHash]

#print axioms literal_key
#print axioms literal_partial
#print axioms changed_challenge
#print axioms product_not_surjective
#print axioms nonzero_not_exact
#print axioms fresh_programs
#print axioms hit_preserves
#print axioms mixed_five_queries
#print axioms mixed_four_insufficient
end ExplainableCrypto.Helios.Computational.TrusteeSimulationControls
