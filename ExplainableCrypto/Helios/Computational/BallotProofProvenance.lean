import ExplainableCrypto.Helios.Computational.RepairedSampling
import ExplainableCrypto.Helios.Computational.AdaptiveBallotSimulation

/-! Accepted repaired-board entries exclude every covered ciphertext of prior
accepted ballots. Honest rejection remains explicit in the provenance bound. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

/-- The implicit aggregate and both explicit components use their actual
historical encryption witnesses. -/
def HonestCoins.coveredWitness (coins : HonestCoins F) (vote : Bool) :
    Option (Fin 2) → BallotWitness F
  | none => (vote,coins.nonce 0 + coins.nonce 1)
  | some i => (if i = 0 then vote else false,coins.nonce i)

def Ballot.coveredStatement {n : Nat} (b : Ballot F G n) (g pk : G)
    (i : Option (Fin n)) : BallotStatement G := ⟨g,pk,b.coveredCiphertext i⟩

theorem strongHonestBallot_covered_statement (hash : StatementHash F G) (g pk : G)
    (vote : Bool) (coins : HonestCoins F) (i : Option (Fin 2)) :
    (strongHonestBallot hash g pk vote coins).coveredStatement g pk i =
      honestProofStatement g pk (coins.coveredWitness vote i) := by
  cases i with
  | none => simp [Ballot.coveredStatement, Ballot.coveredCiphertext,
      strongHonestBallot_aggregate, honestProofStatement, HonestCoins.coveredWitness]
  | some i => fin_cases i <;> rfl

variable [DecidableEq F] [DecidableEq G]

theorem repairedSubmit_acceptance_iff (hash : StatementHash F G) (g pk : G)
    (voter : Fin 3) (board : List (BoardEntry F G)) (b : Ballot F G 2) :
    (repairedSubmit hash g pk voter board b).1 = .accepted ↔
      b.StrongValid hash g pk ∧ b.ExpandedFreshFor (board.map BoardEntry.ballot) := by
  unfold repairedSubmit
  split <;> simp_all
  split <;> simp_all

/-- Actual acceptance excludes a prior covered statement, regardless of either
proof's commitments. This covers component/aggregate cross positions. -/
theorem repairedSubmit_accepted_target_ne (hash : StatementHash F G) (g pk : G)
    (voter : Fin 3) (board : List (BoardEntry F G)) (b old : Ballot F G 2)
    (ha : (repairedSubmit hash g pk voter board b).1 = .accepted)
    (ho : old ∈ board.map BoardEntry.ballot) (i j : Option (Fin 2))
    (pc qc : BallotCommitment G) :
    (b.coveredStatement g pk i,pc) ≠ (old.coveredStatement g pk j,qc) := by
  intro he
  have hct := congrArg (fun key => key.1.ciphertext) he
  exact (repairedSubmit_acceptance_iff hash g pk voter board b).mp ha |>.2 old ho i j hct

/-- Both honest decisions imply actual board membership; nonce freshness is
not substituted for the observed acceptance decisions. -/
theorem repairedCastHonestPair_board_of_accepted (hash : StatementHash F G) (g pk : G)
    (vote : Bool) (aliceCoins bobCoins : HonestCoins F)
    (ha : (repairedCastHonestPair hash g pk vote aliceCoins bobCoins).1 =
      (.accepted,.accepted)) :
    (repairedCastHonestPair hash g pk vote aliceCoins bobCoins).2 =
      [⟨0,strongHonestBallot hash g pk vote aliceCoins⟩,
       ⟨1,strongHonestBallot hash g pk (!vote) bobCoins⟩] := by
  have hfirst := repairedSubmit_accepted hash g pk 0 []
    (strongHonestBallot hash g pk vote aliceCoins) (strongHonestBallot_valid _ _ _ _ _)
    (by simp [Ballot.ExpandedFreshFor])
  simp only [repairedCastHonestPair,hfirst,List.nil_append,Prod.mk.injEq,true_and] at ha ⊢
  have hv := (repairedSubmit_acceptance_iff hash g pk 1 _ _).mp ha
  rw [repairedSubmit_accepted hash g pk 1 _ _ hv.1 hv.2]
  rfl

/-- A matched generated honest statement after an accepted malicious submission
forces rejection in the honest prefix. No board-membership premise remains. -/
theorem accepted_honest_target_match_implies_rejection
    (hash : StatementHash F G) (g pk : G) (vote : Bool)
    (aliceCoins bobCoins : HonestCoins F) (b : Ballot F G 2)
    (ha : (repairedSubmit hash g pk 2
      (repairedCastHonestPair hash g pk vote aliceCoins bobCoins).2 b).1 = .accepted)
    (which : Bool) (i j : Option (Fin 2))
    (hm : b.coveredStatement g pk i = honestProofStatement g pk
      ((if which then bobCoins else aliceCoins).coveredWitness
        (if which then !vote else vote) j)) :
    (repairedCastHonestPair hash g pk vote aliceCoins bobCoins).1 ≠ (.accepted,.accepted) := by
  intro hg
  have hboard := repairedCastHonestPair_board_of_accepted hash g pk vote aliceCoins bobCoins hg
  have hf := (repairedSubmit_acceptance_iff hash g pk 2 _ b).mp ha |>.2
  rw [hboard] at hf
  cases which
  · simp only [Bool.false_eq_true, if_false] at hm
    have he : b.coveredCiphertext i =
        (strongHonestBallot hash g pk vote aliceCoins).coveredCiphertext j := by
      have hs := strongHonestBallot_covered_statement hash g pk vote aliceCoins j
      rw [← hs] at hm
      exact congrArg BallotStatement.ciphertext hm
    exact hf _ (by simp) i j he
  · simp only [if_true] at hm
    have he : b.coveredCiphertext i =
        (strongHonestBallot hash g pk (!vote) bobCoins).coveredCiphertext j := by
      have hs := strongHonestBallot_covered_statement hash g pk (!vote) bobCoins j
      rw [← hs] at hm
      exact congrArg BallotStatement.ciphertext hm
    exact hf _ (by simp) i j he

/-- The match event is defined using actual submissions and generated witness
statements; neither fresh targets nor accepted honest entries are premises. -/
def AcceptedHonestTargetMatch (hash : StatementHash F G) (g pk : G) (vote : Bool)
    (pair : HonestCoins F × HonestCoins F) (b : Ballot F G 2) : Prop :=
  (repairedSubmit hash g pk 2
    (repairedCastHonestPair hash g pk vote pair.1 pair.2).2 b).1 = .accepted ∧
  ∃ (which : Bool) (i j : Option (Fin 2)),
    b.coveredStatement g pk i = honestProofStatement g pk
      ((if which then pair.2 else pair.1).coveredWitness (if which then !vote else vote) j)

theorem accepted_honest_target_match_implies_collision
    (hash : StatementHash F G) (g pk : G)
    (hg : Function.Injective (fun r : F => r • g)) (vote : Bool)
    (pair : HonestCoins F × HonestCoins F) (b : Ballot F G 2)
    (hm : AcceptedHonestTargetMatch hash g pk vote pair b) :
    ¬ ExpandedCollisionFree pair.1 pair.2 := by
  obtain ⟨ha,which,i,j,he⟩ := hm
  have hn := accepted_honest_target_match_implies_rejection hash g pk vote pair.1 pair.2 b
    ha which i j he
  intro hc
  apply hn
  rw [repairedCastHonestPair_eq hash g pk hg vote pair.1 pair.2 hc]

/-- Even a continuation given all honest coins, and choosing a hash and ballot
probabilistically, cannot make this match event more likely than nonce collision.
This bound preserves honest rejection and all continuation failure outcomes. -/
theorem accepted_honest_target_match_probability_le [Fintype F]
    (g pk : G) (hg : Function.Injective (fun r : F => r • g)) (vote : Bool)
    (next : HonestCoins F × HonestCoins F → ProbComp (StatementHash F G × Ballot F G 2)) :
    Pr[fun out => AcceptedHonestTargetMatch out.2.1 g pk vote out.1 out.2.2 |
      (do let pair ← drawHonestPair F; let out ← next pair; pure (pair,out))] ≤
        9 * noncePointBound F := by
  classical
  calc
    _ ≤ Pr[fun pair => ¬ ExpandedCollisionFree pair.1 pair.2 | drawHonestPair F] := by
      rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
      apply ENNReal.tsum_le_tsum
      intro pair
      by_cases hc : ExpandedCollisionFree pair.1 pair.2
      · simp only [hc, not_true_eq_false, ite_false]
        have hz : Pr[fun out => AcceptedHonestTargetMatch out.1 g pk vote pair out.2 |
            next pair] = 0 := by
          apply probEvent_eq_zero_iff.mpr
          intro out _ hm
          exact accepted_honest_target_match_implies_collision out.1 g pk hg vote pair out.2 hm hc
        simp only [bind_pure_comp, probEvent_map, Function.comp_def, hz, mul_zero, le_refl]
      · simp only [hc, not_false_eq_true, ite_true]
        exact mul_le_of_le_one_right' probEvent_le_one
    _ ≤ _ := drawHonestPair_expanded_collision_le

/-- Simulation for a prior accepted ballot cannot alter an accepted submission's
covered target. Freshness is obtained from actual expanded-weeding acceptance. -/
theorem repairedSubmit_accepted_simulation_preserves_target [SampleableType F]
    (hash : StatementHash F G) (g pk : G) (voter : Fin 3)
    (board : List (BoardEntry F G)) (b old : Ballot F G 2)
    (ha : (repairedSubmit hash g pk voter board b).1 = .accepted)
    (ho : old ∈ board.map BoardEntry.ballot) (i j : Option (Fin 2))
    (cache : BallotOracleCache F G)
    (out : (Proof01 F G × Bool) × BallotOracleCache F G)
    (hs : out ∈ support ((strongBallotSimOracle (F := F) (old.coveredStatement g pk j)).run cache))
    (pc : BallotCommitment G) :
    out.2 (b.coveredStatement g pk i,pc) = cache (b.coveredStatement g pk i,pc) := by
  apply strongBallotSimOracle_other_statement _ cache out hs
  intro he
  exact repairedSubmit_accepted_target_ne hash g pk voter board b old ha ho i j pc pc
    (congrArg (fun stmt => (stmt,pc)) he)

#print axioms strongHonestBallot_covered_statement
#print axioms repairedSubmit_acceptance_iff
#print axioms repairedSubmit_accepted_target_ne
#print axioms repairedCastHonestPair_board_of_accepted
#print axioms accepted_honest_target_match_implies_rejection
#print axioms accepted_honest_target_match_implies_collision
#print axioms accepted_honest_target_match_probability_le
#print axioms repairedSubmit_accepted_simulation_preserves_target
end ExplainableCrypto.Helios.Computational
