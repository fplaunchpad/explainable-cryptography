import ExplainableCrypto.Helios.Computational.ElectionProgrammedExtraction

/-! A two-domain preparation and saved-answer-dependent attacker instantiate
complete-source rejection and extraction. Field 257 carries no hardness claim. -/
namespace ExplainableCrypto.Helios.Computational.ElectionProgrammedExtractionControls
open OracleComp OracleSpec ElectionOracle ElectionCache ElectionProgrammedExtraction
local instance : Fact (Nat.Prime 257) := ⟨by decide +kernel⟩
abbrev Scalar := ZMod 257
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar
noncomputable local instance : IsUniformSpec ((Unit →ₒ Scalar) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

def statement : BallotStatement Scalar := ⟨1,3,(2,7)⟩
def commitment : BallotCommitment Scalar := ((4,1),(8,2))
def key : Key Scalar := .key 1 3 4

def prepare : Comp Scalar Scalar (Scalar × Scalar) := do
  let a ← ask key
  let b ← ask (.ballot statement commitment)
  pure (a,b)

def adversary (ballot : Ballot Scalar Scalar 2) (remembered : Scalar × Scalar) :
    Adversary Scalar Scalar Scalar :=
  ⟨fun _ => do let a ← ask key; pure (ballot,a+remembered.1+remembered.2),
   fun saved _ => do let a ← ask key; pure (decide (a = saved))⟩

private theorem hash_one (k : Key Scalar) :
    (ask (F := Scalar) k).IsQueryBoundP (ElectionCacheBudget.isHash (F := Scalar)) 1 := by
  simp [ask,ElectionCacheBudget.isHash]

private theorem prepare_bound : prepare.IsQueryBoundP (ElectionCacheBudget.isHash (F := Scalar)) 2 := by
  unfold prepare
  apply isQueryBoundP_bind (n := 1) (m := 1) (hash_one key)
  intro a _
  simpa only [bind_pure_comp,isQueryBoundP_map_iff] using hash_one (.ballot statement commitment)

private theorem cast_bound (ballot : Ballot Scalar Scalar 2) (remembered : Scalar × Scalar)
    (before : PublicPrefix Scalar Scalar) :
    ((adversary ballot remembered).castBallot before).IsQueryBoundP (ElectionCacheBudget.isHash (F := Scalar)) 1 := by
  simpa only [adversary,bind_pure_comp,isQueryBoundP_map_iff] using hash_one key

private theorem guess_bound (ballot : Ballot Scalar Scalar 2) (remembered : Scalar × Scalar)
    (saved : Scalar) (view : PublicResult Scalar Scalar) :
    ((adversary ballot remembered).guessVote saved view).IsQueryBoundP (ElectionCacheBudget.isHash (F := Scalar)) 1 := by
  simpa only [adversary,bind_pure_comp,isQueryBoundP_map_iff] using hash_one key

private theorem injective_generator : Function.Injective (fun r : Scalar => r • (1 : Scalar)) := by
  intro a b h; simpa [smul_eq_mul] using h

private theorem loss_coercion : ENNReal.ofReal (150 / 257 : ℝ) = (150 : ENNReal) / 257 := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- Actual full-source honest rejection after both preparation queries has an
explicit bound strictly below one; final querying callbacks remain present. -/
theorem rejection_after_queries (ballot : Ballot Scalar Scalar 2) :
    Pr[fun out => out.1.1.1.beforeTally.honestDecisions ≠ (.accepted,.accepted) |
      runBallotOracle (source (fun p => p.trusteeKeyProof.response.val) 1 prepare (adversary ballot)) ∅] ≤
      9 / 256 + 150 / 257 := by
  have h := prepared_rejection_le (fun p => p.trusteeKeyProof.response.val) 1 injective_generator
    prepare (adversary ballot) 2 1 prepare_bound (cast_bound ballot)
  norm_num [noncePointBound] at h ⊢
  rw [loss_coercion] at h
  simpa only [div_eq_mul_inv] using h

/-- The concrete joint algorithm retains the actual preparation and both
querying callbacks, with all loss terms instantiated. -/
theorem joint_after_queries (ballot : Ballot Scalar Scalar 2) (δ : ENNReal) :
    let a := Pr[fun out => out.1.1.1.decision = .accepted |
      runBallotOracle (source (fun p => p.trusteeKeyProof.response.val) 1 prepare (adversary ballot)) ∅]
    (a-(9/256+150/257)-60*δ)*(δ-1/257)^3 ≤
      Pr[fun out => out.isSome | joint (fun p => p.trusteeKeyProof.response.val) 1 prepare (adversary ballot) 19] := by
  have h := joint_le (fun p => p.trusteeKeyProof.response.val) 1 injective_generator
    prepare (adversary ballot) 2 1 1 prepare_bound (cast_bound ballot) (guess_bound ballot) δ
  norm_num [noncePointBound] at h ⊢
  rw [loss_coercion] at h
  simpa only [div_eq_mul_inv] using h

/-- These loss constants permit a positive lower bound at acceptance mass one.
This is arithmetic nonvacuity, not a claim that the actual acceptance mass is one. -/
theorem losses_allow_positive_bound :
    (0 : ENNReal) < (1-(9/256+150/257)-60*(1/200)) * ((1/200)-(1/257))^3 := by
  have hn : (0 : NNReal) < (1-(9/256+150/257)-60*(1/200)) * ((1/200)-(1/257))^3 := by
    change (0 : ℝ) < ((1-(9/256+150/257)-60*(1/200) : NNReal) * ((1/200)-(1/257))^3 : NNReal)
    norm_num [NNReal.coe_sub_def]
  simpa [ENNReal.coe_sub,ENNReal.coe_div] using (ENNReal.coe_lt_coe.mpr hn)

/-- Key-cache answers and saved preparation values remain observable by the
actual final callback; its answer is not a constant. -/
theorem saved_answer_changes_guess (ballot : Ballot Scalar Scalar 2) (view : PublicResult Scalar Scalar) :
    let cache : Cache Scalar Scalar := (∅ : Cache Scalar Scalar).cacheQuery key 5
    run ((adversary ballot (0,0)).guessVote 5 view) cache = pure (true,cache) ∧
    run ((adversary ballot (0,0)).guessVote 6 view) cache = pure (false,cache) := by
  have hr : run (ask (F := Scalar) key) ((∅ : Cache Scalar Scalar).cacheQuery key 5) =
      pure (5,(∅ : Cache Scalar Scalar).cacheQuery key 5) := by simp [run_ask]
  dsimp only [adversary]
  simp only [run_bind,hr,run_pure,pure_bind]
  norm_num [show (5 : Scalar) ≠ 6 by decide]

#print axioms rejection_after_queries
#print axioms joint_after_queries
#print axioms losses_allow_positive_bound
#print axioms saved_answer_changes_guess
end ExplainableCrypto.Helios.Computational.ElectionProgrammedExtractionControls
