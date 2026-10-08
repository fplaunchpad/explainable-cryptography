import ExplainableCrypto.Helios.Computational.RepairedSubmissionOracle
import ExplainableCrypto.Helios.Computational.BallotForkAcceptance

/-! Select an actual accepted covered proof for replay. Rejected executions
produce a proof that always fails; they cannot inflate extraction success. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F]

def RepairedSubmissionResult.Accepted (out : RepairedSubmissionResult F G) : Prop :=
  out.honest.1 = (.accepted,.accepted) ∧ out.decision = .accepted

instance (out : RepairedSubmissionResult F G) : Decidable out.Accepted := by
  unfold RepairedSubmissionResult.Accepted; infer_instance

def replayRejectedProof (g : G) : Proof01 F G := ⟨⟨g,0,0,0⟩,⟨0,0,0,0⟩⟩

/-- Internal replay selection only; the original public submission result is
unchanged. Both full challenges are retained on the accepting branch. -/
noncomputable def repairedSubmissionTargetOracle [Fintype F] (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (i : Option (Fin 2)) :
    BallotOracleComp F G (BallotStatement G × Proof01 F G) := do
  let out ← (simulateQ (ballotProgrammedImpl g pk) (repairedSubmissionOracle g pk vote attacker)).run .empty
  pure (out.1.ballot.coveredStatement g pk i,
    if out.1.Accepted then out.1.ballot.coveredProof i else replayRejectedProof g)

omit [DecidableEq F] [DecidableEq G] [SampleableType F] in
private theorem rejected_not_valid (g pk : G) (hg : g ≠ 0) (ct : Ciphertext G) (c : F) :
    ¬ (replayRejectedProof g).Valid (fun _ => c) g pk ct := by
  intro hv
  exact hg (by simpa [replayRejectedProof,Branch.Valid] using hv.1.1.symm)

theorem replayRejectedProof_verification_zero (g pk : G) (hg : g ≠ 0) (ct : Ciphertext G)
    (cache : BallotOracleCache F G) :
    Pr[fun out => out.1 |
      runBallotOracle (strongBallotVerifyOracle ⟨g,pk,ct⟩ (replayRejectedProof g)) cache] = 0 := by
  apply probEvent_eq_zero_iff.mpr
  intro out ho ht
  obtain ⟨c,hc,hv⟩ := runBallotOracle_verify_true_cached _ _ cache out ho ht
  exact rejected_not_valid g pk hg ct c hv

/-- Actual live verification of the selected target is exactly acceptance of
the honest prefix and attacker submission. Rejected branches contribute zero. -/
theorem repairedSubmissionTargetOracle_acceptance_eq [Fintype F] (g pk : G) (hg : g ≠ 0)
    (vote : Bool) (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2))
    (i : Option (Fin 2)) :
    Pr[fun out => out.1 | runBallotOracle
      (ballotVerificationGame (repairedSubmissionTargetOracle g pk vote attacker i)) ∅] =
    Pr[fun out => out.1.1.Accepted |
      runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker)] := by
  classical
  simp only [ballotVerificationGame,repairedSubmissionTargetOracle,bind_assoc,pure_bind,
    runBallotOracle_bind]
  change Pr[fun out => out.1 | (do
    let out ← runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker)
    runBallotOracle (strongBallotVerifyOracle (out.1.1.ballot.coveredStatement g pk i)
      (if out.1.1.Accepted then out.1.1.ballot.coveredProof i else replayRejectedProof g)) out.2)] = _
  rw [probEvent_bind_eq_tsum,probEvent_eq_tsum_ite]
  apply tsum_congr
  intro out
  by_cases hs : out ∈ support (runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker))
  · by_cases ha : out.1.1.Accepted
    · rw [if_pos ha]
      rw [repairedSubmissionOracle_accepted_live g pk vote attacker out hs ha.1 ha.2 i]
      simp [ha]
    · rw [if_neg ha]
      simp [ha,Ballot.coveredStatement,replayRejectedProof_verification_zero g pk hg]
  · simp [probOutput_eq_zero_of_not_mem_support hs]

omit [DecidableEq F] [DecidableEq G] [SampleableType F] in
private theorem injective_generator_ne_zero (g : G) (hg : Function.Injective (fun r : F => r • g)) :
    g ≠ 0 := by
  intro hz
  have h := hg (show (1 : F) • g = (0 : F) • g by simp [hz])
  exact one_ne_zero h

/-- The lowered target program retains the entire submission's query budget;
the proof-selection guard adds no queries. -/
theorem repairedSubmissionTargetOracle_query_bound [Fintype F] (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (i : Option (Fin 2))
    (n : Nat) (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := F)) n) :
    (repairedSubmissionTargetOracle g pk vote attacker i).IsQueryBoundP
      (isBallotHashQuery (F := F)) (n+15) := by
  unfold repairedSubmissionTargetOracle
  apply isQueryBoundP_bind (n := n+15) (m := 0)
    (ballotProgrammed_query_bound g pk _ (n+15) (repairedSubmissionOracle_query_bound g pk vote attacker n hb) .empty)
  simp

noncomputable def repairedSubmission_extract [Fintype F] (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (i : Option (Fin 2)) (n : Nat) :=
  ballotForkExtract (ballotForkComplete (repairedSubmissionTargetOracle g pk vote attacker i)) (n+15)

section Probability
local instance : Inhabited F := ⟨0⟩
noncomputable local instance [Fintype F] : IsUniformSpec ((Unit →ₒ F) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

/-- Replay lower bound for an actual accepted submission's chosen covered proof,
including the programmed honest prefix and all adaptive raw attacker queries. -/
theorem repairedSubmission_extract_accepted_le [Fintype F] (g pk : G)
    (hg : Function.Injective (fun r : F => r • g)) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (i : Option (Fin 2))
    (n : Nat) (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := F)) n) :
    let acc := Pr[fun out => out.1.1.Accepted |
      runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker)]
    acc * (acc / (n+16 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤
      Pr[fun out => out.isSome | repairedSubmission_extract g pk vote attacker i n] := by
  have h := ballotFork_acceptance_extraction_le (repairedSubmissionTargetOracle g pk vote attacker i) (n+15)
    (repairedSubmissionTargetOracle_query_bound g pk vote attacker i n hb)
  dsimp only at h ⊢
  rw [repairedSubmissionTargetOracle_acceptance_eq g pk (injective_generator_ne_zero g hg)] at h
  simpa only [repairedSubmission_extract,Nat.cast_add,Nat.cast_ofNat,add_assoc,
    show (15 : ENNReal)+1=16 by norm_num] using h

/-- The accepted-submission bound carries the explicit honest-rejection loss;
it never assumes the honest prefix accepted unconditionally. -/
theorem repairedSubmission_extract_le [Fintype F] (g pk : G)
    (hg : Function.Injective (fun r : F => r • g)) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (i : Option (Fin 2))
    (n : Nat) (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := F)) n) :
    let accepted := Pr[fun out => out.1.1.decision = .accepted |
      runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker)]
    let a := accepted - (9 * noncePointBound F + ENNReal.ofReal (90 / (Fintype.card F : ℝ)))
    a * (a / (n+16 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤
      Pr[fun out => out.isSome | repairedSubmission_extract g pk vote attacker i n] := by
  classical
  let run := runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker)
  have hsplit : Pr[fun out => out.1.1.decision = .accepted | run] ≤
      Pr[fun out => out.1.1.Accepted | run] +
        Pr[fun out => out.1.1.honest.1 ≠ (.accepted,.accepted) | run] := by
    apply le_trans ?_ (probEvent_or_le run (fun out => out.1.1.Accepted)
      (fun out => out.1.1.honest.1 ≠ (.accepted,.accepted)))
    apply probEvent_mono
    intro out _ ha
    by_cases hh : out.1.1.honest.1 = (.accepted,.accepted)
    · exact Or.inl ⟨hh,ha⟩
    · exact Or.inr hh
  have hl : Pr[fun out => out.1.1.decision = .accepted | run] -
      (9 * noncePointBound F + ENNReal.ofReal (90 / (Fintype.card F : ℝ))) ≤
        Pr[fun out => out.1.1.Accepted | run] := by
    have hbad : Pr[fun out => out.1.1.honest.1 ≠ (.accepted,.accepted) | run] ≤
        9 * noncePointBound F + ENNReal.ofReal (90 / (Fintype.card F : ℝ)) :=
      repairedSubmissionOracle_prefix_rejection_le (F := F) (G := G) g pk hg vote attacker
    have hsum := add_le_add (le_refl (Pr[fun out => out.1.1.Accepted | run])) hbad
    exact tsub_le_iff_right.mpr (hsplit.trans hsum)
  apply le_trans ?_ (repairedSubmission_extract_accepted_le g pk hg vote attacker i n hb)
  dsimp only [run] at hl
  apply mul_le_mul' hl
  apply tsub_le_tsub_right
  simp only [div_eq_mul_inv]
  exact mul_le_mul' hl le_rfl

end Probability

attribute [local irreducible] repairedSubmissionTargetOracle

/-- Successful composed replay still yields the actual encryption bit/nonce
relation. Binding it back to the accepted source execution is audited separately. -/
theorem repairedSubmission_extract_valid [Fintype F] (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (i : Option (Fin 2)) (n : Nat)
    (stmt : BallotStatement G) (wit : BallotWitness F)
    (ho : some (stmt,wit) ∈ support (repairedSubmission_extract g pk vote attacker i n)) :
    stmt.Witnesses wit := by
  unfold repairedSubmission_extract at ho
  apply ballotFork_extract_valid (F := F) (G := G)
    (ballotForkComplete (repairedSubmissionTargetOracle g pk vote attacker i)) (n+15) stmt wit
  with_reducible exact ho

/-- Successful extraction is tied to the chosen ciphertext of a supported
actual accepted submission, not merely to an unrelated valid statement. -/
theorem repairedSubmission_extract_origin [Fintype F] (g pk : G) (hg : g ≠ 0) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (i : Option (Fin 2)) (n : Nat)
    (stmt : BallotStatement G) (wit : BallotWitness F)
    (ho : some (stmt,wit) ∈ support (repairedSubmission_extract g pk vote attacker i n)) :
    stmt.Witnesses wit ∧ ∃ out ∈ support
      (runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker)),
      out.1.1.Accepted ∧ stmt = out.1.1.ballot.coveredStatement g pk i := by
  have hv := repairedSubmission_extract_valid g pk vote attacker i n stmt wit ho
  have hs : ∃ (p : Proof01 F G) (cache : BallotOracleCache F G) (c : F),
      ((stmt,p),cache) ∈ support (runBallotOracle
        (ballotForkComplete (repairedSubmissionTargetOracle g pk vote attacker i)) ∅) ∧
      p.Valid (fun _ => c) stmt.generator stmt.publicKey stmt.ciphertext := by
    unfold repairedSubmission_extract at ho
    apply ballotFork_extract_source
      (ballotForkComplete (repairedSubmissionTargetOracle g pk vote attacker i)) (n+15) stmt wit
    with_reducible exact ho
  obtain ⟨p,cache,c,hs,hp⟩ := hs
  simp only [ballotForkComplete,repairedSubmissionTargetOracle,bind_assoc,pure_bind,
    runBallotOracle_bind] at hs
  have pureRun {α : Type} (x : α) (cache : BallotOracleCache F G) :
      runBallotOracle (pure x) cache = pure (x,cache) := by simp [runBallotOracle]
  simp only [pureRun,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at hs
  obtain ⟨out,hout,answer,hanswer,he⟩ := hs
  have hstmt : stmt = out.1.1.ballot.coveredStatement g pk i := congrArg (fun x => x.1.1) he
  have hproof : p = if out.1.1.Accepted then out.1.1.ballot.coveredProof i else replayRejectedProof g :=
    congrArg (fun x => x.1.2) he
  have haccept : out.1.1.Accepted := by
    by_contra hn
    rw [if_neg hn] at hproof
    rw [hproof,hstmt] at hp
    exact rejected_not_valid g pk hg _ c hp
  exact ⟨hv,out,hout,haccept,hstmt⟩

#print axioms replayRejectedProof_verification_zero
#print axioms repairedSubmissionTargetOracle_acceptance_eq
#print axioms repairedSubmissionTargetOracle_query_bound
#print axioms repairedSubmission_extract_accepted_le
#print axioms repairedSubmission_extract_le
#print axioms repairedSubmission_extract_valid
#print axioms repairedSubmission_extract_origin
end ExplainableCrypto.Helios.Computational
