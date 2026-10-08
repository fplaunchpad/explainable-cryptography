import ExplainableCrypto.Helios.Computational.Trustee
import ExplainableCrypto.Helios.Computational.NonzeroSimulationBridge

/-! Reuse pinned Schnorr HVZK for the actual trustee equations. Mapping the
scalar-group theorem works for both G and G×G, with no sampler on G and no
surjectivity assumption on the product-group statement. -/
namespace ExplainableCrypto.Helios.Computational.TrusteeSimulation
open OracleComp OracleSpec
variable {F H : Type} [Field F] [AddCommGroup H] [Module F H] [SampleableType F]

def transcript (base key : H) : ProbComp (H × F × F) :=
  Schnorr.simTranscript F H base key

def proof (base key : H) (challenge response : F) : SchnorrProof F H :=
  ⟨response • base - challenge • key,response⟩

omit [SampleableType F] in
/-- The simulated proof satisfies the actual verification equation. -/
theorem proof_valid (base key : H) (challenge response : F) :
    (proof base key challenge response).Valid (fun _ => challenge) base key := by
  simp [proof,SchnorrProof.Valid]

variable [Fintype F] [DecidableEq F]

/-- Exact full-field simulation, derived by mapping VCVio's scalar Schnorr
HVZK theorem. The group need not itself be sampleable or cyclic. -/
theorem full_eq (base : H) (secret : F) :
    𝒮[do let r ← uniformSample F
          let c ← uniformSample F
          pure ((r • base,c,r+c*secret) : H × F × F)] =
      𝒮[transcript base (secret • base)] := by
  have h := Schnorr.sigma_hvzk F F (1 : F) secret secret (by simp)
  have hm := evalSPMF_map_eq_of_evalSPMF_eq h
    (fun t : F × F × F => (t.1 • base,t.2.1,t.2.2))
  simpa [ChallengeVerifyProtocol.realTranscript,Schnorr.sigma,transcript,
    Schnorr.simTranscript,map_bind,smul_eq_mul,sub_smul,mul_smul] using hm

/-- The historical nonzero nonce costs at most one scalar point probability.
This is transcript simulation; oracle hits are accounted for separately. -/
theorem nonzero_distance (base : H) (secret : F) :
    tvDist (do let r ← sampleNonzero F
               let c ← uniformSample F
               pure ((r • base,c,r+c*secret) : H × F × F))
      (transcript base (secret • base)) ≤ (Fintype.card F : ℝ)⁻¹ := by
  have hb := tvDist_bind_right_le
    (fun r : F => do let c ← uniformSample F; pure ((r • base,c,r+c*secret) : H × F × F))
    (sampleNonzero F) (uniformSample F)
  have he := full_eq base secret
  unfold tvDist at hb ⊢
  rw [← he]
  exact hb.trans sampleNonzero_uniform_tv_le

omit [DecidableEq F] in
/-- A fixed simulated commitment has at most one scalar preimage for each
challenge. Injectivity is sufficient even for the decryption product group. -/
theorem commitment_probability_le (base key target : H)
    (hg : Function.Injective (fun r : F => r • base)) :
    Pr[fun t => t.1 = target | transcript (F := F) base key] ≤
      (Fintype.card F : ENNReal)⁻¹ := by
  classical
  unfold transcript Schnorr.simTranscript
  apply probEvent_bind_le_of_forall_le
  intro c _
  simp only [bind_pure_comp,probEvent_map,Function.comp_def]
  let f := fun z : F => z • base - c • key
  have hf : Function.Injective f := fun x y h => hg (by simpa [f] using congrArg (fun v : H => v + c • key) h)
  change Pr[fun z => f z = target | uniformSample F] ≤ _
  rcases Classical.em (∃ z, f z = target) with ht | ht
  · obtain ⟨z,rfl⟩ := ht
    simpa only [hf.eq_iff,probEvent_eq_eq_probOutput,probOutput_uniformSample] using
      (le_refl ((Fintype.card F : ENNReal)⁻¹))
  · have hn : ∀ z, f z ≠ target := by simpa using ht
    simp [hn]

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- The actual decryption statement derives injectivity from its first coordinate. -/
theorem partial_injective {G : Type} [AddCommGroup G] [Module F G] (g : G)
    (hg : Function.Injective (fun r : F => r • g)) (ct : Ciphertext G) :
    Function.Injective (fun r : F => r • (g,ct.1)) := by
  intro x y h
  exact hg (congrArg Prod.fst h)

#print axioms proof_valid
#print axioms full_eq
#print axioms nonzero_distance
#print axioms commitment_probability_le
#print axioms partial_injective
end ExplainableCrypto.Helios.Computational.TrusteeSimulation
