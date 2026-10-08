import ExplainableCrypto.Helios.Computational.RepairedSubmissionSource
import ExplainableCrypto.Helios.Computational.BallotJointReplay
import ExplainableCrypto.Helios.Computational.BallotWitnessConsistency

/-! Joint conditional replay of the original accepted post-prefix submission.
The witnesses and their common ballot are derived from the algorithm. Success
probability and computational efficiency remain separate obligations. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F] [Fintype F]

noncomputable def repairedSubmission_joint_extract (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (n : Nat) :=
  ballotJointReplay (repairedSubmissionSourceOracle g pk vote attacker)
    (repairedSubmissionSelect g pk) (n+15)

attribute [local irreducible] repairedSubmissionSourceOracle

/-- Joint success returns the original accepting submission and witnesses for
both its actual components and its actual implicit aggregate. -/
theorem repairedSubmission_joint_extract_valid (g pk : G) (hg : g ≠ 0) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (n : Nat)
    (result : RepairedSubmissionResult F G) (w : Option (Fin 2) → BallotWitness F)
    (ho : some (result,w) ∈ support (repairedSubmission_joint_extract g pk vote attacker n)) :
    result.Accepted ∧ (∀ i, (result.ballot.coveredStatement g pk i).Witnesses (w i)) ∧
      ∃ out ∈ support (runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker)),
        out.1.1 = result := by
  obtain ⟨hv,cache,hcache⟩ := ballotJointReplay_valid _ _ (n+15) result w ho
  have ha : result.Accepted := by
    by_contra hn
    obtain ⟨c,hproof⟩ := (hv none).2
    simp only [repairedSubmissionSelect,if_neg hn,Ballot.coveredStatement] at hproof
    exact hg (by simpa [replayRejectedProof,Branch.Valid] using hproof.1.1.symm)
  rw [repairedSubmissionSource_runtime,support_map] at hcache
  obtain ⟨out,hout,he⟩ := hcache
  exact ⟨ha,fun i => (hv i).1,out,hout,congrArg Prod.fst he⟩

/-- Applying the algebraic contract to witnesses produced by the actual joint
algorithm yields nonce consistency and the integer at-most-one constraint. -/
theorem repairedSubmission_joint_extract_consistent (g pk : G)
    (hg : Function.Injective (fun r : F => r • g)) (h2 : (2 : F) ≠ 0) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (n : Nat)
    (result : RepairedSubmissionResult F G) (w : Option (Fin 2) → BallotWitness F)
    (ho : some (result,w) ∈ support (repairedSubmission_joint_extract g pk vote attacker n)) :
    result.Accepted ∧ (w none).2 = (w (some 0)).2 + (w (some 1)).2 ∧
      (w (some 0)).1.toNat + (w (some 1)).1.toNat = (w none).1.toNat ∧
      (w (some 0)).1.toNat + (w (some 1)).1.toNat ≤ 1 := by
  have hg0 : g ≠ 0 := by
    intro he
    have hh : (1 : F) = 0 := hg (by simp [he])
    exact one_ne_zero hh
  obtain ⟨ha,hw,_⟩ := repairedSubmission_joint_extract_valid g pk hg0 vote attacker n result w ho
  exact ⟨ha,(result.ballot.covered_witnesses_sum g pk hg w hw).1,
    result.ballot.covered_witnesses_atMostOne g pk hg h2 w hw⟩

#print axioms repairedSubmission_joint_extract_valid
#print axioms repairedSubmission_joint_extract_consistent
end ExplainableCrypto.Helios.Computational
