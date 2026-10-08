import ExplainableCrypto.Helios.Computational.HonestPrefixRejection
import ExplainableCrypto.Helios.Computational.RepairedBoardOracleControls

/-! A larger finite field makes the actual rejection bound nontrivial; small
historical fixtures retain rejection and zero aggregate nonces independently. -/
namespace ExplainableCrypto.Helios.Computational.HonestPrefixRejectionControls
open OracleComp OracleSpec
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩
abbrev Scalar := ZMod 101
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar

private theorem generator_injective : Function.Injective (fun r : Scalar => r • (1 : Scalar)) := by
  intro a b h
  simpa [smul_eq_mul] using h

noncomputable def realPrefix := runBallotProofReal (1 : Scalar) 3
  (repairedCastHonestPairOracle (F := Scalar) 1 3 false) (∅,false)
noncomputable def programmedPrefix := runBallotProgrammed (1 : Scalar) 3
  (repairedCastHonestPairOracle (F := Scalar) 1 3 false)

theorem real_rejection_nontrivial :
    Pr[fun out => out.1.1 ≠ (.accepted,.accepted) | realPrefix] ≤ 9 / 100 := by
  have h := repairedCastHonestPairOracle_real_rejection_le (1 : Scalar) 3 generator_injective false (∅,false)
  norm_num [noncePointBound] at h ⊢
  exact h

theorem programmed_rejection_nontrivial :
    Pr[fun out => out.1.1.1 ≠ (.accepted,.accepted) | programmedPrefix] ≤ ENNReal.ofReal (9909 / 10100 : ℝ) := by
  have h := repairedCastHonestPairOracle_programmed_rejection_le (1 : Scalar) 3 generator_injective false
  have he : 9 * noncePointBound Scalar + ENNReal.ofReal (90 / (Fintype.card Scalar : ℝ)) =
      ENNReal.ofReal (9909 / 10100 : ℝ) := by
    have h9 : (9 : ENNReal) * 100⁻¹ = ENNReal.ofReal (9 / 100 : ℝ) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num [div_eq_mul_inv]
    norm_num only [noncePointBound,ZMod.card,Nat.reduceSub]
    rw [h9,← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    norm_num
  exact h.trans_eq he

theorem programmed_acceptance_positive :
    0 < Pr[fun out => out.1.1.1 = (.accepted,.accepted) | programmedPrefix] := by
  have hf : NeverFail programmedPrefix := inferInstance
  have hc := probEvent_compl programmedPrefix (fun out => out.1.1.1 ≠ (.accepted,.accepted))
  simp only [not_not,probFailure_eq_zero,tsub_zero] at hc
  apply pos_iff_ne_zero.mpr
  intro hz
  rw [hz,add_zero] at hc
  have hn := programmed_rejection_nontrivial
  rw [hc] at hn
  norm_num [ENNReal.one_le_ofReal] at hn

section ZeroGenerator
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] [SampleableType K]

omit [Field K] [Fintype K] in
private theorem runZero_pure {α : Type} (x : α) (cache : BallotOracleCache K K) :
    runBallotOracle (pure x) cache = pure (x,cache) := by simp [runBallotOracle]

omit [Fintype K] in
private theorem zero_ciphertext (vote : Bool) (coins : HonestCoins K)
    (cache : BallotOracleCache K K) (out : Ballot K K 2 × BallotOracleCache K K)
    (ho : out ∈ support (runBallotOracle (strongHonestBallotWithCoinsOracle 0 0 vote coins) cache)) :
    out.1.ciphertext 0 = (0,0) := by
  simp only [strongHonestBallotWithCoinsOracle,runBallotOracle_bind] at ho
  simp only [runZero_pure,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨a,ha,b,hb,c,hc,rfl⟩ := ho
  simp [assembleHonestBallot,encryptWith]

omit [Fintype K] in
private theorem zero_prefix_rejects (coins : HonestCoins K × HonestCoins K)
    (run : ((Decision × Decision) × List (BoardEntry K K)) × BallotOracleCache K K)
    (hrun : run ∈ support (runBallotOracle
      (repairedCastHonestPairWithCoinsOracle 0 0 false coins.1 coins.2) ∅)) :
    run.1.1 ≠ (.accepted,.accepted) := by
  intro ha
  simp only [repairedCastHonestPairWithCoinsOracle,runBallotOracle_bind,runZero_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at hrun
  obtain ⟨alice,halice,first,hfirst,bob,hbob,second,hsecond,rfl⟩ := hrun
  have hf := repairedSubmitOracle_accepted (0 : K) 0 0 [] alice.1 alice.2 first hfirst (congrArg Prod.fst ha)
  have hs := repairedSubmitOracle_accepted (0 : K) 0 1 first.1.2 bob.1 bob.2 second hsecond
    (congrArg Prod.snd ha)
  have ha0 := zero_ciphertext false coins.1 ∅ alice halice
  have hb0 := zero_ciphertext true coins.2 first.2 bob hbob
  exact hs.2.1 alice.1 (by simp [hf.2.2]) (some 0) (some 0) (hb0.trans ha0.symm)

/-- Omitting generator injectivity makes the real bound false: the zero-generator
execution always rejects. This is an invalid-parameter control, not a protocol attack. -/
theorem zero_generator_rejection_certain :
    Pr[fun out => out.1.1 ≠ (.accepted,.accepted) |
      runBallotProofReal (0 : K) 0 (repairedCastHonestPairOracle (F := K) 0 0 false)
        (∅,false)] = 1 := by
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (repairedCastHonestPairOracle_real_eq 0 0 false (∅,false))]
  apply probEvent_eq_one_iff.mpr
  refine ⟨by simp,?_⟩
  intro out ho
  simp only [support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨coins,hcoins,run,hrun,rfl⟩ := ho
  exact zero_prefix_rejects coins run hrun

end ZeroGenerator

/-- The original independently derived rejection fixture remains possible in
the historical sampler; the new bound does not assert rejection is impossible. -/
theorem original_rejection_fixture_retained :
    (ExecutionControls.aliceCoins,BallotProofProvenanceControls.rejectedBobCoins) ∈
      support (drawHonestPair RepairControls.Scalar) :=
  BallotProofProvenanceControls.rejection_fixture_reachable

#print axioms real_rejection_nontrivial
#print axioms programmed_rejection_nontrivial
#print axioms programmed_acceptance_positive
#print axioms zero_generator_rejection_certain
#print axioms original_rejection_fixture_retained
end ExplainableCrypto.Helios.Computational.HonestPrefixRejectionControls
