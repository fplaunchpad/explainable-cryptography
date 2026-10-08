import ExplainableCrypto.Helios.Computational.RepairedSubmissionCoverage
import ExplainableCrypto.Helios.Computational.BallotJointReplayBound

/-! Quantitative joint extraction for the actual programmed prefix, subsequent
raw attacker and original submission. Honest rejection and the uniform focused
challenge collision losses remain explicit. Efficiency and full election
integration are separate obligations. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F] [Fintype F]
local instance submissionJointBoundInhabited : Inhabited F := ⟨0⟩
noncomputable local instance submissionJointBoundUniform : IsUniformSpec ((Unit →ₒ F) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

attribute [local irreducible] repairedSubmissionSourceOracle

/-- The joint extractor's success bound uses actual joint acceptance and the
derived source budget; no witness or same-source correspondence is assumed. -/
theorem repairedSubmission_joint_extract_accepted_le (g pk : G) (hg : g ≠ 0) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (n : Nat)
    (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := F)) n) (δ : ENNReal) :
    let α := Pr[fun out => out.1.1.Accepted |
      runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker)]
    (α - 3*(n+16 : ENNReal)*δ) * (δ - (Fintype.card F : ENNReal)⁻¹)^3 ≤
      Pr[fun out => out.isSome | repairedSubmission_joint_extract g pk vote attacker n] := by
  have h := ballotJointReplay_selection_le (repairedSubmissionSourceOracle g pk vote attacker)
    (repairedSubmissionSelect g pk) (n+15) δ
  dsimp only at h ⊢
  rw [repairedSubmissionPath_selection_probability g pk hg vote attacker n hb] at h
  simpa only [repairedSubmission_joint_extract,Nat.cast_add,Nat.cast_ofNat,add_assoc,
    show (15 : ENNReal)+1=16 by norm_num] using h

/-- Actual accepted-submission probability loses only the previously bounded
honest-prefix rejection event when restricted to joint acceptance. -/
theorem repairedSubmission_joint_acceptance_loss (g pk : G)
    (hg : Function.Injective (fun r : F => r • g)) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) :
    Pr[fun out => out.1.1.decision = .accepted |
      runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker)] -
      (9 * noncePointBound F + ENNReal.ofReal (90 / (Fintype.card F : ℝ))) ≤
    Pr[fun out => out.1.1.Accepted |
      runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker)] := by
  apply tsub_le_iff_right.mpr
  apply le_trans ?_ (add_le_add le_rfl
    (repairedSubmissionOracle_prefix_rejection_le (F := F) (G := G) g pk hg vote attacker))
  apply probEvent_le_add_of_imp_or
  intro out _ ha
  by_cases hh : out.1.1.honest.1 = (.accepted,.accepted)
  · exact Or.inl ⟨hh,ha⟩
  · exact Or.inr hh

/-- Joint replay with honest-rejection and simulation loss retained. Both
subtractions are truncated in ENNReal; this is a finite probabilistic bound,
not yet a PPT theorem or a full election-secrecy reduction. -/
theorem repairedSubmission_joint_extract_le (g pk : G)
    (hg : Function.Injective (fun r : F => r • g)) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (n : Nat)
    (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := F)) n) (δ : ENNReal) :
    let accepted := Pr[fun out => out.1.1.decision = .accepted |
      runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker)]
    let a := accepted - (9 * noncePointBound F + ENNReal.ofReal (90 / (Fintype.card F : ℝ)))
    (a - 3*(n+16 : ENNReal)*δ) * (δ - (Fintype.card F : ENNReal)⁻¹)^3 ≤
      Pr[fun out => out.isSome | repairedSubmission_joint_extract g pk vote attacker n] := by
  have hg0 : g ≠ 0 := by
    intro he
    have h : (1 : F) = 0 := hg (by simp [he])
    exact one_ne_zero h
  apply le_trans ?_ (repairedSubmission_joint_extract_accepted_le g pk hg0 vote attacker n hb δ)
  exact mul_le_mul' (tsub_le_tsub_right (repairedSubmission_joint_acceptance_loss g pk hg vote attacker) _) le_rfl

#print axioms repairedSubmission_joint_extract_accepted_le
#print axioms repairedSubmission_joint_acceptance_loss
#print axioms repairedSubmission_joint_extract_le
end ExplainableCrypto.Helios.Computational
