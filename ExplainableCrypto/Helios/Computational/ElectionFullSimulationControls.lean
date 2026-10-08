import ExplainableCrypto.Helios.Computational.ElectionFullSimulation

/-! A complete prepared-game instance with nontrivial simulation loss and
observable cached-query behavior. The small field carries no hardness claim. -/
namespace ExplainableCrypto.Helios.Computational.ElectionFullSimulationControls
open OracleComp OracleSpec ElectionOracle ElectionCache ElectionCacheBudget ElectionFullSimulation
local instance : Fact (Nat.Prime 257) := ⟨by decide +kernel⟩
abbrev Scalar := ZMod 257
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar

def request : Key Scalar := .key 1 3 4

def adversary (remembered : Scalar) (ballot : Ballot Scalar Scalar 2) : Adversary Scalar Scalar Scalar :=
  ⟨fun _ => do let a ← ask request; pure (ballot,a+remembered),
   fun saved _ => do let a ← ask request; pure (decide (a = saved))⟩

private theorem query_bound : (ask (F := Scalar) request).IsQueryBoundP (isHash (F := Scalar)) 1 := by
  simp [ask,isQueryBoundP_query_iff,isHash]

private theorem cast_bound (remembered : Scalar) (ballot : Ballot Scalar Scalar 2)
    (before : PublicPrefix Scalar Scalar) :
    ((adversary remembered ballot).castBallot before).IsQueryBoundP (isHash (F := Scalar)) 1 := by
  simpa only [adversary,Nat.add_zero] using
    isQueryBoundP_bind query_bound (fun _ _ => (isQueryBoundP_pure _ _ 0))

/-- An actual preparation query and two querying attacker callbacks instantiate
 the full original-source theorem. The bound is strictly below one. -/
theorem prepared_nontrivial (ballot : Ballot Scalar Scalar 2) :
    tvDist ((fun out => ((out.1,false),out.2)) <$> run
      (ElectionExtraction.preparedSource (fun p => p.trusteeKeyProof.response.val) (1 : Scalar)
        (ask request) (fun remembered => adversary remembered ballot)) ∅)
      (preparedSim (fun p => p.trusteeKeyProof.response.val) (1 : Scalar)
        (ask request) (fun remembered => adversary remembered ballot)) ≤ 139 / 257 := by
  have hg : Function.Injective (fun r : Scalar => r • (1 : Scalar)) := by
    intro a b h; simpa [smul_eq_mul] using h
  have h := prepared_distance_le (fun p => p.trusteeKeyProof.response.val) (1 : Scalar) hg
    (ask request) (fun remembered => adversary remembered ballot) 1 1 query_bound
    (fun remembered before => cast_bound remembered ballot before)
  norm_num at h ⊢
  exact h

theorem loss_below_one : (139 : ℝ) / 257 < 1 := by norm_num

/-- The guessing callback distinguishes saved states on the retained cache.
 Thus the complete-game control does not use a constant guessing action. -/
theorem guess_observes_saved (ballot : Ballot Scalar Scalar 2) (view : PublicResult Scalar Scalar) :
    let cache : Cache Scalar Scalar := (∅ : Cache Scalar Scalar).cacheQuery request 5
    run ((adversary 0 ballot).guessVote 5 view) cache = pure (true,cache) ∧
    run ((adversary 0 ballot).guessVote 6 view) cache = pure (false,cache) := by
  have hr : run (ask (F := Scalar) request) ((∅ : Cache Scalar Scalar).cacheQuery request 5) =
      pure (5,(∅ : Cache Scalar Scalar).cacheQuery request 5) := by simp [run_ask]
  dsimp only [adversary]
  simp only [run_bind,hr,run_pure,pure_bind]
  norm_num [show (5 : Scalar) ≠ 6 by decide]

/-- An earlier prefix collision cannot be cleared by finishing or by guessing. -/
theorem prefix_flag_survives (secret : Scalar) (adv : Adversary Scalar Scalar Scalar)
    (before : PublicPrefix Scalar Scalar) (cache : Cache Scalar Scalar) (out : Output Scalar Scalar)
    (ho : out ∈ support (afterSim secret adv ((before,true),cache))) : out.1.2 = true := by
  simp only [afterSim,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨cast,_,finished,_,guessed,_,rfl⟩ := ho
  rfl

#print axioms prepared_nontrivial
#print axioms loss_below_one
#print axioms guess_observes_saved
#print axioms prefix_flag_survives
end ExplainableCrypto.Helios.Computational.ElectionFullSimulationControls
