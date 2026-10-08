import ExplainableCrypto.Helios.Computational.ElectionTrusteeSimulation
import ExplainableCrypto.Helios.Computational.TrusteeSimulationControls

/-! Concrete proof/collision controls complement the independent multiplicative
pair experiment. These small groups do not carry hardness assumptions. -/
namespace ExplainableCrypto.Helios.Computational.ElectionTrusteeSimulationControls
open OracleComp OracleSpec ElectionOracle ElectionTrusteeSimulation TrusteeReachableSimulation
abbrev Scalar := ZMod 11
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar

def cts : Fin 2 → Ciphertext Scalar := ![(8,4),(2,1)]
def shares : Fin 2 → Scalar := ![2,6]
def tag0 := Key.decryption (1 : Scalar) 3 (cts 0) (shares 0)
def tag1 := Key.decryption (1 : Scalar) 3 (cts 1) (shares 1)
def first := TrusteeOracleSimulation.finish tag0 (∅ : Cache Scalar Scalar) ((1,8),0,1)
def second := TrusteeOracleSimulation.finish tag1 first.2 ((2,4),0,2)

private theorem coins_supported (ct : Ciphertext Scalar) (share c z : Scalar)
    (cache : Cache Scalar Scalar) :
    TrusteeOracleSimulation.finish (Key.decryption 1 3 ct share) cache
      (z • ((1,ct.1) : Scalar × Scalar) - c • (3,share),c,z) ∈
      support ((partialSim (1 : Scalar) 3 ct share).run cache) := by
  simp only [partialSim,TrusteeOracleSimulation.sim,StateT.run,support_map]
  refine ⟨_,?_,rfl⟩
  simp only [TrusteeSimulation.transcript,Schnorr.simTranscript,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff]
  exact ⟨c,by simp,z,by simp,rfl⟩

/-- Both simulated proofs can be fresh and have independently specified commitments. -/
theorem two_fresh_supported :
    let out := ((![first.1.1,second.1.1],first.1.2 || second.1.2),second.2)
    out ∈ support ((simPair (1 : Scalar) 3 cts shares).run ∅) ∧
      out.1.2 = false ∧ (out.1.1 0).commitment = (1,8) ∧ (out.1.1 1).commitment = (2,4) := by
  refine ⟨?_,?_,?_,?_⟩
  · simp only [simPair,pair,StateT.run,support_bind,support_pure,
      Set.mem_iUnion,Set.mem_singleton_iff]
    refine ⟨first,?_,second,?_,rfl⟩
    · simpa [first,tag0,cts,shares,StateT.run] using coins_supported (cts 0) (shares 0) 0 1 ∅
    · simpa [second,tag1,cts,shares,StateT.run,show (2 : Scalar)*2=4 by decide] using coins_supported (cts 1) (shares 1) 0 2 first.2
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- A first-step collision survives a fresh second step. -/
theorem first_flag_sticky (p0 p1 : PartialProof Scalar Scalar) (cache : Cache Scalar Scalar) :
    (pair (fun c => pure ((p0,true),c)) (fun c => pure ((p1,false),c))).run cache =
      pure ((![p0,p1],true),cache) := by simp [pair,StateT.run]

theorem second_flag_detected (p0 p1 : PartialProof Scalar Scalar) (cache : Cache Scalar Scalar) :
    (pair (fun c => pure ((p0,false),c)) (fun c => pure ((p1,true),c))).run cache =
      pure ((![p0,p1],true),cache) := by simp [pair,StateT.run]

/-- The public publication preserves rejection and the retained empty board. -/
theorem rejected_publication (before : PublicPrefix Scalar Scalar)
    (submission : Ballot Scalar Scalar 2) (proofs : Fin 2 → PartialProof Scalar Scalar) :
    (publication before submission (.reusedCiphertext,[]) (fun _ => 0) proofs).decision =
      .reusedCiphertext ∧
    (publication before submission (.reusedCiphertext,[]) (fun _ => 0) proofs).board = [] ∧
    (publication before submission (.reusedCiphertext,[]) (fun _ => 0) proofs).submission = submission := by
  exact ⟨rfl,rfl,rfl⟩

/-- A zero-prior-query finishing bound is strictly below the maximal distance. -/
theorem finish_bound_nontrivial : (2*(0 : ℝ)+9) * (11 : ℝ)⁻¹ < 1 := by norm_num

#print axioms two_fresh_supported
#print axioms first_flag_sticky
#print axioms second_flag_detected
#print axioms rejected_publication
#print axioms finish_bound_nontrivial
end ExplainableCrypto.Helios.Computational.ElectionTrusteeSimulationControls
