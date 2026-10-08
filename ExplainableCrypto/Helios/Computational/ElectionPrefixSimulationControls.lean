import ExplainableCrypto.Helios.Computational.ElectionPrefixSimulation
import ExplainableCrypto.Helios.Computational.ElectionCacheControls

/-! Observable fingerprint, rejection and full-cache reconstruction controls.
Literal modular fixtures complement the independent reachable-cache enumeration. -/
namespace ExplainableCrypto.Helios.Computational.ElectionPrefixSimulationControls
open OracleComp OracleSpec ElectionOracle ElectionCache ElectionPrefixSimulation
open ElectionOracleControls (Scalar keyRequest partialRequest populated)
open ElectionCacheControls (statement commitment)

/-- A ballot-phase result retains the prior key/decryption domains. -/
theorem restored_other_domains :
    let out := restore populated ((),((project populated).cacheQuery (statement,commitment) 3,true))
    out.2 keyRequest = some 5 ∧ out.2 partialRequest = some 7 ∧
      out.2 (.ballot statement commitment) = some 3 ∧ out.1.2 = true := by
  simp [restore,replace,populated,QueryCache.cacheQuery,keyRequest,partialRequest]

/-- Returning the ballot projection as the whole cache would erase a prior key answer. -/
theorem lost_domain_counterexample :
    replace (∅ : Cache Scalar Nat) (project populated) ≠ populated := by
  intro h
  have hk := congrArg (fun c => c keyRequest) h
  simp [replace,populated,QueryCache.cacheQuery,keyRequest,partialRequest] at hk

def fingerprint (p : PublicParameters Scalar Scalar) : Nat :=
  p.trusteeKeyProof.commitment.val + p.trusteeKeyProof.response.val

def proofA : SchnorrProof Scalar Scalar := ⟨4,8⟩
def proofB : SchnorrProof Scalar Scalar := ⟨5,9⟩

/-- The fingerprint is computed from the actual key proof, rather than fixed metadata. -/
theorem fingerprint_observes_proof :
    (publication fingerprint 1 3 proofA ((.accepted,.accepted),[])).fingerprint = 12 ∧
    (publication fingerprint 1 3 proofB ((.accepted,.accepted),[])).fingerprint = 14 := by
  decide +kernel

/-- Simulated publication retains the original honest rejection decision. -/
theorem rejection_retained :
    (publication fingerprint 1 3 proofA ((.accepted,.reusedCiphertext),[])).honestDecisions =
      (.accepted,.reusedCiphertext) ∧
    (publication fingerprint 1 3 proofA ((.accepted,.reusedCiphertext),[])).parameters.trusteeKeyProof = proofA := by
  exact ⟨rfl,rfl⟩

/-- A later observable read sees the restored key answer and cannot clear the private flag. -/
theorem continuation_keeps_flag (before : PublicPrefix Scalar Nat) :
    follow (fun _ => ask keyRequest) ((before,true),populated) =
      pure (((before,5),true),populated) := by
  simp [follow,run_ask,populated,QueryCache.cacheQuery,keyRequest,partialRequest]

theorem prefix_bound_nontrivial : (7*(0 : ℝ)+91) / 101 < 1 := by norm_num

#print axioms restored_other_domains
#print axioms lost_domain_counterexample
#print axioms fingerprint_observes_proof
#print axioms rejection_retained
#print axioms continuation_keeps_flag
#print axioms prefix_bound_nontrivial
end ExplainableCrypto.Helios.Computational.ElectionPrefixSimulationControls
