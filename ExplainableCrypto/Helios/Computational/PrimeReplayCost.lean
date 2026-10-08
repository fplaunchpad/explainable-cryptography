import ExplainableCrypto.Helios.Computational.PrimeReplayExtraction

/-! Derived total interaction bounds for the explicit source and its own replay.
These count oracle interactions; encoded local execution and machine costs remain open. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {q : Nat} [Fact q.Prime] {G : Type} [AddCommGroup G]
  [Module (ZMod q) G] [DecidableEq G]
attribute [local irreducible] drawPrimeNoncePair strongHonestBallotWithNoncesOracle repairedSubmitOracle
attribute [local irreducible] repairedSubmissionPrimeSourceOracle

/-- Count two actual nonce pairs, six proof requests, three verifications and
all attacker interactions, retaining every short-circuit rejection branch. -/
theorem repairedSubmissionPrimeOracle_total_bound (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2))
    (m : Nat) (hb : ∀ view, (attacker view).IsTotalQueryBound m) :
    (repairedSubmissionPrimeOracle g pk vote attacker).IsTotalQueryBound (m+19) := by
  have hn : (drawPrimeNoncePair (q := q)).IsTotalQueryBound 2 := by
    unfold drawPrimeNoncePair
    change IsTotalQueryBound _ (1+(1+0))
    exact isTotalQueryBound_bind samplePrimeNonzero_total_bound (fun _ =>
      isTotalQueryBound_bind samplePrimeNonzero_total_bound (fun _ => trivial))
  have hl := liftComp_total_query_bound (BallotProofOracleSpec (ZMod q) G) _ 2 hn
  have hp (v : Bool) (rs : ZMod q × ZMod q) :
      (strongHonestBallotWithNoncesOracle g pk v rs).IsTotalQueryBound 3 := by
    unfold strongHonestBallotWithNoncesOracle ballotProofQuery
    exact ⟨by norm_num,fun _ => ⟨by norm_num,fun _ => ⟨by norm_num,fun _ => trivial⟩⟩⟩
  have hs (voter : Fin 3) (board : List (BoardEntry (ZMod q) G)) (b : Ballot (ZMod q) G 2) :
      (liftComp (repairedSubmitOracle g pk voter board b) (BallotProofOracleSpec (ZMod q) G)).IsTotalQueryBound 3 :=
    liftComp_total_query_bound _ _ 3 (repairedSubmitOracle_total_query_bound g pk voter board b)
  unfold repairedSubmissionPrimeOracle repairedSubmissionWithNoncePairs
  rw [show m+19 = 2+(3+(3+(2+(3+(3+(m+(3+0))))))) by omega]
  apply isTotalQueryBound_bind hl
  intro rs0
  apply isTotalQueryBound_bind (hp vote rs0)
  intro alice
  apply isTotalQueryBound_bind (hs 0 [] alice)
  intro first
  apply isTotalQueryBound_bind hl
  intro rs1
  apply isTotalQueryBound_bind (hp (!vote) rs1)
  intro bob
  apply isTotalQueryBound_bind (hs 1 first.2 bob)
  intro second
  dsimp only
  apply isTotalQueryBound_bind (liftComp_total_query_bound _ _ m (hb _))
  intro ballot
  exact isTotalQueryBound_bind (hs 2 second.2 ballot) (fun _ => trivial)

/-- The default computable prime scalar sampler discharges the handler's cost
premise; finite state projection does not change interaction counts. -/
theorem repairedSubmissionPrimeSource_total_bound (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2))
    (m : Nat) (hb : ∀ view, (attacker view).IsTotalQueryBound m) :
    (repairedSubmissionPrimeSourceOracle g pk vote attacker).IsTotalQueryBound (4*(m+19)) := by
  have h := ballotProgrammed_total_query_bound g pk primeScalarSampler_total_bound _ (m+19)
    (repairedSubmissionPrimeOracle_total_bound g pk vote attacker m hb) .empty
  have he := runBallotFiniteProgrammed_eq g pk (repairedSubmissionPrimeOracle g pk vote attacker) .empty
  rw [BallotFiniteProgrammedState.denote_empty] at he
  rw [← he] at h
  have hf : ((simulateQ (ballotFiniteProgrammedImpl g pk)
      (repairedSubmissionPrimeOracle g pk vote attacker)).run .empty).IsTotalQueryBound (4*(m+19)) :=
    (isQueryBound_map_iff _ _ (4*(m+19)) _ _).mp h
  unfold repairedSubmissionPrimeSourceOracle
  exact (isQueryBound_map_iff _ _ _ _ _).mpr hf

/-- Original execution plus all three replay attempts for the actual explicit
source; no primitive sampler-cost or replay-correspondence premise remains. -/
theorem repairedSubmissionPrimeBits_extract_total_bound (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2))
    (n m : Nat) (hb : ∀ view, (attacker view).IsTotalQueryBound m) :
    (repairedSubmissionPrimeBits_extract g pk vote attacker n).IsTotalQueryBound (16*(m+19)) := by
  rw [repairedSubmissionPrimeBits_extract_eq]
  have h := ballotJointReplay_total_query_bound (repairedSubmissionPrimeSourceOracle g pk vote attacker)
    (repairedSubmissionSelect g pk) (n+15) (4*(m+19))
    (repairedSubmissionPrimeSource_total_bound g pk vote attacker m hb)
  simpa only [← Nat.mul_assoc,show 4*4=16 from rfl] using h

#print axioms repairedSubmissionPrimeOracle_total_bound
#print axioms repairedSubmissionPrimeSource_total_bound
#print axioms repairedSubmissionPrimeBits_extract_total_bound
end ExplainableCrypto.Helios.Computational
