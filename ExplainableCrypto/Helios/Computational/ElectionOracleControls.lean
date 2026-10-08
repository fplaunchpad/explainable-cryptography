import ExplainableCrypto.Helios.Computational.ElectionOracle
import ExplainableCrypto.Helios.Computational.RepairControls

/-! Independent p=23, q=11 transcripts and mixed-domain cache controls.
The exponent fixtures use the existing encoding r ↦ 2^r mod 23. They make
no hardness claim for this small group or for the deliberately simple hashes. -/
namespace ExplainableCrypto.Helios.Computational.ElectionOracleControls
open OracleComp OracleSpec ElectionOracle
abbrev Scalar := ZMod 11

def keyRequest : Key Nat := .key 2 8 16
def partialRequest : Key Nat := .decryption 2 8 (3,13) 4 (16,12)
def emptyCache : Cache Scalar Nat := fun _ => none
def populated : Cache Scalar Nat :=
  (emptyCache.cacheQuery keyRequest 5).cacheQuery partialRequest 7

def mixed : Comp Scalar Nat (List Scalar) := do
  let a ← ask keyRequest
  let b ← ask partialRequest
  let c ← ask keyRequest
  let d ← ask partialRequest
  pure [a,b,c,d]

theorem mixed_hit_control :
    run mixed populated = pure ([5,7,5,7],populated) := by
  have hn : keyRequest ≠ partialRequest := by decide
  simp only [mixed,run_bind,run_ask,run_pure,populated,
    QueryCache.cacheQuery_self,QueryCache.cacheQuery_of_ne _ _ hn,pure_bind]

/-- Two misses sample twice; both subsequent hits retain their original answers. -/
theorem mixed_miss_control :
    run mixed emptyCache = (do
      let a ← uniformSample Scalar
      let b ← uniformSample Scalar
      pure ([a,b,a,b],(emptyCache.cacheQuery keyRequest a).cacheQuery partialRequest b)) := by
  have hn : keyRequest ≠ partialRequest := by decide
  simp only [mixed,run_bind,run_ask,run_pure,
    QueryCache.cacheQuery_self,QueryCache.cacheQuery_of_ne _ _ hn,
    QueryCache.cacheQuery_of_ne _ _ hn.symm,emptyCache,
    pure_bind,bind_assoc]

/-- Resetting the cache cannot implement the saved five/seven transcript. -/
theorem miss_not_constant (out : List Scalar × Cache Scalar Nat) :
    run mixed emptyCache ≠ pure out := by
  intro h
  have first := congrArg (fun oa => (fun o => o.1.headD 0) <$> oa) h
  rw [mixed_miss_control] at first
  simp only [map_bind,map_pure,List.headD_cons] at first
  have hu : (⋃ x : Scalar, ({x} : Set Scalar)) = Set.univ := by ext x; simp
  have hs : (Set.univ : Set Scalar) = {out.1.headD 0} := by
    simpa [hu] using congrArg (fun oa : ProbComp Scalar => support oa) first
  have h0 : (0 : Scalar) = out.1.headD 0 := by
    have hm : (0 : Scalar) ∈ ({out.1.headD 0} : Set Scalar) := by rw [← hs]; trivial
    exact hm
  have h1 : (1 : Scalar) = out.1.headD 0 := by
    have hm : (1 : Scalar) ∈ ({out.1.headD 0} : Set Scalar) := by rw [← hs]; trivial
    exact hm
  exact (by decide : (0 : Scalar) ≠ 1) (h0.trans h1.symm)

theorem key_request_control :
    keyWithCoins (1 : Scalar) 3 4 = (do
      let c ← ask (.key (1 : Scalar) 3 4)
      pure (⟨4,4+c*3⟩ : SchnorrProof Scalar Scalar)) := by
  simp [keyWithCoins,smul_eq_mul]

theorem partial_request_control :
    partialWithCoins (1 : Scalar) 3 4 (8,7) = (do
      let c ← ask (.decryption (1 : Scalar) 3 (8,7) 2 (4,10))
      pure (⟨(4,10),4+c*3⟩ : SchnorrProof Scalar (Scalar × Scalar))) := by
  norm_num [partialWithCoins,partialDecrypt,smul_eq_mul]
  rw [show (32 : Scalar) = 10 by decide,show (24 : Scalar) = 2 by decide]

def contextHashes : StrongCryptoHashes Scalar Scalar where
  ballot _ _ _ _ := 5
  key _ pk _ := if pk = 3 then 5 else 7
  decryption _ _ _ share _ := if share = 2 then 5 else 7
  fingerprint _ := 37

/-- Removing the public-key or share coordinate cannot represent these hashes. -/
theorem changed_context_control :
    simulateQ (functionImpl contextHashes) (ask (.key (1 : Scalar) 3 4)) = pure 5 ∧
    simulateQ (functionImpl contextHashes) (ask (.key (1 : Scalar) 4 4)) = pure 7 ∧
    simulateQ (functionImpl contextHashes)
      (ask (.decryption (1 : Scalar) 3 (8,7) 2 (4,10))) = pure 5 ∧
    simulateQ (functionImpl contextHashes)
      (ask (.decryption (1 : Scalar) 3 (8,7) 3 (4,10))) = pure 7 := by
  simp [ask_function,contextHashes,show (4 : Scalar) ≠ 3 by decide,
    show (3 : Scalar) ≠ 2 by decide]

theorem key_transcript_control :
    simulateQ (functionImpl contextHashes) (keyWithCoins (1 : Scalar) 3 4) =
      pure (⟨4,8⟩ : SchnorrProof Scalar Scalar) := by
  rw [keyWithCoins_function]
  congr 1

theorem partial_transcript_control :
    simulateQ (functionImpl contextHashes) (partialWithCoins (1 : Scalar) 3 4 (8,7)) =
      pure (⟨(4,10),8⟩ : SchnorrProof Scalar (Scalar × Scalar)) := by
  rw [partialWithCoins_function]
  congr 1

/-- The changed response nine fails both independent modular equations. -/
theorem bad_response_control :
    2 ^ 8 % 23 = 16 * 8 ^ 5 % 23 ∧ 3 ^ 8 % 23 = 12 * 4 ^ 5 % 23 ∧
    2 ^ 9 % 23 ≠ 16 * 8 ^ 5 % 23 ∧ 3 ^ 9 % 23 ≠ 12 * 4 ^ 5 % 23 := by
  decide +kernel

#print axioms mixed_hit_control
#print axioms mixed_miss_control
#print axioms miss_not_constant
#print axioms key_request_control
#print axioms partial_request_control
#print axioms changed_context_control
#print axioms key_transcript_control
#print axioms partial_transcript_control
#print axioms bad_response_control
end ExplainableCrypto.Helios.Computational.ElectionOracleControls
