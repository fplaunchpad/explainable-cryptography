import ExplainableCrypto.Helios.Computational.ElectionDDHRealSource

/-! Random-mask secrecy for the complete comparison source. The secret belongs
only to this mathematical hybrid, never to the public-input DDH reduction. -/
namespace ExplainableCrypto.Helios.Computational.ElectionDDHSource
open OracleComp OracleSpec ElectionOracle ElectionCache
open OracleComp.ProgramLogic OracleComp.ProgramLogic.Relational
open ElectionProgrammedSource (State Source raw trustee evaluate evaluate_bind evaluate_pure)
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

private def finishGuess {Saved : Type} (g pk : G) (secret : F)
    (adversary : Adversary F G Saved) (before : PublicPrefix F G)
    (submission : Ballot F G 2) (saved : Saved)
    (cast : Decision × List (BoardEntry F G)) : Source F G (PublicResult F G × Bool) := do
  let cts := boardTally cast.2
  let shares := fun j => partialDecrypt secret (cts j)
  let proofs ← trustee (ElectionTrusteeSimulation.simPair g pk cts shares)
  let view := ElectionTrusteeSimulation.publication before submission cast shares proofs
  let guess ← raw g pk (adversary.guessVote saved view)
  pure (view,guess)

private def fixedGuess {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (secret : F) (adversary : Init → Adversary F G Saved)
    (initial : Init) (vote : Bool) : Source F G (PublicResult F G × Bool) := do
  let key ← trustee (TrusteeReachableSimulation.keySim g pk)
  let coins ← raw g pk (liftProb (drawKnown (F := F)))
  let honest ← ballots g pk A T coins.1 coins.2.1 coins.2.2 vote
  let before := ElectionPrefixSimulation.publication fingerprint g pk key honest.1
  let made ← raw g pk ((adversary initial).castBallot before)
  let cast ← raw g pk (liftBallot (repairedSubmitOracle g pk 2 before.board made.1))
  finishGuess g pk secret (adversary initial) before made.1 made.2 cast

omit [Fintype F] in
private theorem fixed_mask_shift {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A : G) (secret z : F) (adversary : Init → Adversary F G Saved)
    (initial : Init) (vote : Bool) :
    fixedGuess fingerprint g pk A (z • g) secret adversary initial false =
      fixedGuess fingerprint g pk A ((z-voteScalar (F := F) vote) • g) secret adversary initial vote := by
  have hb (t a b : F) : ballots g pk A (z • g) t a b false =
      ballots g pk A ((z-voteScalar (F := F) vote) • g) t a b vote := by
    unfold ballots challengePair
    rw [ElectionDDHConstruction.paired_mask_shift g pk A z t a b vote]
  simp only [fixedGuess,hb]

omit [Fintype F] in
private theorem fixed_random_eq {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A : G) (secret : F) (adversary : Init → Adversary F G Saved)
    (initial : Init) (vote : Bool) (s : State F G) (live : BallotOracleCache F G) :
    evalSPMF (do let z ← uniformSample F
                 evaluate (fixedGuess fingerprint g pk A (z • g) secret adversary initial false) s live) =
      evalSPMF (do let z ← uniformSample F
                   evaluate (fixedGuess fingerprint g pk A (z • g) secret adversary initial vote) s live) := by
  apply evalSPMF_ext
  intro out
  apply probOutput_eq_of_relTriple_eqRel (x := out)
  refine relTriple_bind_uniformSample_bij (f := fun z : F => z-voteScalar (F := F) vote)
    (fun z => ?_) (sub_left_injective.bijective_of_finite)
  rw [fixed_mask_shift fingerprint g pk A secret z adversary initial vote]
  exact relTriple_refl _

private abbrev FinalOutput (F G : Type) :=
  ((PublicResult F G × Bool) × State F G) × BallotOracleCache F G

private def score (vote : Bool) (out : FinalOutput F G) : FinalOutput F G :=
  (((out.1.1.1,decide (out.1.1.2=vote)),out.1.2),out.2)

omit [Fintype F] in
private theorem completed_run {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (secret : F) (prepare : Comp F G Init)
    (adversary : Init → Adversary F G Saved) (s : State F G) (live : BallotOracleCache F G) :
    evaluate (completedReal fingerprint g pk A T secret prepare adversary) s live =
      (do let initial ← evaluate (raw g 0 prepare) s live
          let vote ← uniformSample Bool
          score vote <$> evaluate (fixedGuess fingerprint g pk A T secret adversary initial.1.1 vote)
            initial.1.2 initial.2) := by
  simp only [completedReal,preparedPrefix,fixedGuess,finishAfterCast,finishGuess,
    bind_assoc,pure_bind,evaluate_bind,evaluate_pure,raw_prob,
    bind_map_left,pure_bind,map_bind,map_pure,score]


omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem fair_score (oa : ProbComp (FinalOutput F G)) :
    Pr[fun out => out.1.1.2 = true | do let vote ← uniformSample Bool; score vote <$> oa] =
      (2:ENNReal)⁻¹ := by
  simp only [map_eq_bind_pure_comp,Function.comp_def]
  rw [probEvent_bind_bind_swap,probEvent_bind_eq_tsum]
  have hc (out : FinalOutput F G) :
      Pr[fun x => x.1.1.2 = true | do let vote ← uniformSample Bool; pure (score vote out)] =
        (2:ENNReal)⁻¹ := by
    cases h : out.1.1.2 <;>
      norm_num [score,h,Finset.filter_insert,Finset.filter_singleton]
  simp_rw [hc]
  rw [ENNReal.tsum_mul_right,tsum_probOutput_eq_one' (by simp),one_mul]

omit [Fintype F] in
/-- The actual complete secret-using comparison wins with probability exactly
one half under a uniform random mask. Preparation, all oracle answers, rejection,
trustee publication and adaptive guessing are retained. This is a mathematical
hybrid; its explicit secret is not an input to the DDH reduction. -/
theorem completed_random_win {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A : G) (secret : F) (prepare : Comp F G Init)
    (adversary : Init → Adversary F G Saved) (s : State F G) (live : BallotOracleCache F G) :
    Pr[fun out => out.1.1.2 = true | do
      let z ← uniformSample F
      evaluate (completedReal fingerprint g pk A (z • g) secret prepare adversary) s live] =
        (2:ENNReal)⁻¹ := by
  simp only [completed_run]
  rw [probEvent_bind_bind_swap]
  rw [probEvent_bind_eq_tsum]
  have hc (initial : (Init × State F G) × BallotOracleCache F G) :
      Pr[fun out => out.1.1.2 = true | do
        let z ← uniformSample F
        let vote ← uniformSample Bool
        score vote <$> evaluate (fixedGuess fingerprint g pk A (z • g) secret adversary initial.1.1 vote)
          initial.1.2 initial.2] = (2:ENNReal)⁻¹ := by
    rw [probEvent_bind_bind_swap]
    have he : evalSPMF (do
        let vote ← uniformSample Bool
        let z ← uniformSample F
        score vote <$> evaluate (fixedGuess fingerprint g pk A (z • g) secret adversary initial.1.1 vote)
          initial.1.2 initial.2) = evalSPMF (do
        let vote ← uniformSample Bool
        score vote <$> (do let z ← uniformSample F
                           evaluate (fixedGuess fingerprint g pk A (z • g) secret adversary initial.1.1 false)
                             initial.1.2 initial.2)) := by
      apply evalSPMF_bind_congr'
      intro vote
      rw [← map_bind,evalSPMF_map,evalSPMF_map,
        ← fixed_random_eq fingerprint g pk A secret adversary initial.1.1 vote initial.1.2 initial.2]
    exact (probEvent_congr' (fun _ _ => Iff.rfl) he).trans (fair_score _)
  simp_rw [hc]
  rw [ENNReal.tsum_mul_right,tsum_probOutput_eq_one' (by simp),one_mul]

#print axioms completed_random_win
end ExplainableCrypto.Helios.Computational.ElectionDDHSource
