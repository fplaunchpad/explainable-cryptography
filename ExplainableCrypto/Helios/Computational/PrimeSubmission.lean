import ExplainableCrypto.Helios.Computational.PrimeSamplers
import ExplainableCrypto.Helios.Computational.RepairedFiniteProgrammed

/-! Substitute explicit nonce pairs in the actual finite submission runtime.
The full returned state is preserved in distribution; path-based replay requires
its own correspondence and is not inferred from this distribution theorem. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {q : Nat} [Fact q.Prime] {G : Type} [AddCommGroup G]
  [Module (ZMod q) G] [DecidableEq G]

/-- Factor exactly the two honest nonce-pair draws; retain actual proof requests,
verification, adaptive attacker, public decisions and retained boards. -/
def repairedSubmissionWithNoncePairs (draw : ProbComp (ZMod q × ZMod q))
    (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2)) :
    OracleComp (BallotProofOracleSpec (ZMod q) G) (RepairedSubmissionResult (ZMod q) G) := do
  let rs0 ← liftComp draw _
  let alice ← strongHonestBallotWithNoncesOracle g pk vote rs0
  let first ← liftComp (repairedSubmitOracle g pk 0 [] alice) _
  let rs1 ← liftComp draw _
  let bob ← strongHonestBallotWithNoncesOracle g pk (!vote) rs1
  let second ← liftComp (repairedSubmitOracle g pk 1 first.2 bob) _
  let honest := ((first.1,second.1),second.2)
  let ballot ← liftComp (attacker honest) _
  let cast ← liftComp (repairedSubmitOracle g pk 2 honest.2 ballot) _
  pure ⟨honest,ballot,cast.1,cast.2⟩

/-- Factoring did not change the historical source or any rejection branch. -/
theorem repairedSubmissionWithNoncePairs_original (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2)) :
    repairedSubmissionWithNoncePairs (drawNoncePair (ZMod q)) g pk vote attacker =
      repairedSubmissionOracle g pk vote attacker := by
  simp [repairedSubmissionWithNoncePairs,repairedSubmissionOracle,
    repairedCastHonestPairOracle,strongHonestBallotOracle,bind_assoc]

private def primeSubmissionRun {A : Type}
    (g pk : G) (oa : OracleComp (BallotProofOracleSpec (ZMod q) G) A)
    (state : BallotFiniteProgrammedState (ZMod q) G) (live : BallotFiniteCache (ZMod q) G) :=
  runBallotFiniteCache ((simulateQ (ballotFiniteProgrammedImpl g pk) oa).run state) live

private theorem primeSubmissionRun_bind {A B : Type} (g pk : G)
    (oa : OracleComp (BallotProofOracleSpec (ZMod q) G) A)
    (next : A → OracleComp (BallotProofOracleSpec (ZMod q) G) B)
    (state : BallotFiniteProgrammedState (ZMod q) G) (live : BallotFiniteCache (ZMod q) G) :
    primeSubmissionRun g pk (oa >>= next) state live = (do
      let out ← primeSubmissionRun g pk oa state live
      primeSubmissionRun g pk (next out.1.1) out.1.2 out.2) := by
  simp [primeSubmissionRun,runBallotFiniteCache,simulateQ_bind,StateT.run_bind]

private theorem primeSubmissionRun_lift {A : Type} (g pk : G) (oa : ProbComp A)
    (state : BallotFiniteProgrammedState (ZMod q) G) (live : BallotFiniteCache (ZMod q) G) :
    primeSubmissionRun g pk (liftComp oa _) state live =
      (fun a => ((a,state),live)) <$> oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [primeSubmissionRun,runBallotFiniteCache]
  | query_bind t next ih =>
    rw [liftComp_bind,primeSubmissionRun_bind]
    have hq : primeSubmissionRun g pk
        (liftComp (liftM (unifSpec.query t) : ProbComp _) _) state live =
        (fun a => ((a,state),live)) <$> (liftM (unifSpec.query t) : ProbComp _) := by
      change primeSubmissionRun g pk
        (liftM ((BallotProofOracleSpec (ZMod q) G).query (.inl (.inl t)))) state live = _
      simp [primeSubmissionRun,runBallotFiniteCache,ballotFiniteProgrammedImpl,
        ballotFiniteProgrammedRaw,ballotFiniteCacheImpl,QueryImpl.add,StateT.run]
      change (fun a => ((a.1,state),a.2)) <$>
        ((fun a => (a,live)) <$> (liftM (unifSpec.query t) : ProbComp _)) = _
      rw [Functor.map_map]
    rw [hq]
    simp only [bind_map_left,map_bind]
    exact bind_congr ih

/-- Actual nonce sampling through both finite interpreters leaves their complete
state untouched, including nonempty caches and duplicate request history. -/
theorem drawPrimeNoncePair_finite_state (g pk : G)
    (state : BallotFiniteProgrammedState (ZMod q) G) (live : BallotFiniteCache (ZMod q) G) :
    runBallotFiniteCache ((simulateQ (ballotFiniteProgrammedImpl g pk)
      (liftComp (drawPrimeNoncePair (q := q)) (BallotProofOracleSpec (ZMod q) G))).run state) live =
      (fun rs => ((rs,state),live)) <$> drawPrimeNoncePair :=
  primeSubmissionRun_lift g pk _ state live

/-- Explicit nonzero pairs used in the actual protocol source. -/
def repairedSubmissionPrimeOracle (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2)) :=
  repairedSubmissionWithNoncePairs drawPrimeNoncePair g pk vote attacker

/-- Complete stateful runtime preservation under every subsequent probabilistic
use. Initial cache entries, sticky flag and request history need no invariant. -/
theorem repairedSubmissionPrime_runtime_bind {A : Type} (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2))
    (state : BallotFiniteProgrammedState (ZMod q) G) (live : BallotFiniteCache (ZMod q) G)
    (next : ((RepairedSubmissionResult (ZMod q) G × BallotFiniteProgrammedState (ZMod q) G) ×
      BallotFiniteCache (ZMod q) G) → ProbComp A) (x : A) :
    Pr[= x | runBallotFiniteCache ((simulateQ (ballotFiniteProgrammedImpl g pk)
      (repairedSubmissionPrimeOracle g pk vote attacker)).run state) live >>= next] =
    Pr[= x | runBallotFiniteCache ((simulateQ (ballotFiniteProgrammedImpl g pk)
      (repairedSubmissionOracle g pk vote attacker)).run state) live >>= next] := by
  change Pr[= x | primeSubmissionRun g pk (repairedSubmissionPrimeOracle g pk vote attacker)
    state live >>= next] = Pr[= x | primeSubmissionRun g pk
    (repairedSubmissionOracle g pk vote attacker) state live >>= next]
  rw [← repairedSubmissionWithNoncePairs_original]
  simp only [repairedSubmissionPrimeOracle,repairedSubmissionWithNoncePairs,
    primeSubmissionRun_bind,primeSubmissionRun_lift,bind_map_left,bind_assoc]
  rw [drawPrimeNoncePair_bind]
  apply probOutput_bind_congr
  intro rs hrs
  apply probOutput_bind_congr
  intro alice ha
  apply probOutput_bind_congr
  intro first hf
  exact drawPrimeNoncePair_bind _ _

/-- The actual empty-initial-state finite runtime preserves the entire output
law. Both caches and the ordered request history are retained. -/
theorem repairedSubmissionPrime_runtime (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2)) :
    𝒮[runBallotFiniteProgrammed g pk (repairedSubmissionPrimeOracle g pk vote attacker)] =
      𝒮[runBallotFiniteProgrammed g pk (repairedSubmissionOracle g pk vote attacker)] := by
  apply evalSPMF_ext
  intro x
  simpa only [runBallotFiniteProgrammed,bind_pure] using
    repairedSubmissionPrime_runtime_bind g pk vote attacker .empty ∅ pure x

/-- The raw finite source now uses explicit nonce enumeration as well as the
existing computable scalar sampler. Replay transport remains a separate proof. -/
def repairedSubmissionPrimeSourceOracle (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2)) :
    BallotOracleComp (ZMod q) G (RepairedSubmissionResult (ZMod q) G) :=
  Prod.fst <$> (simulateQ (ballotFiniteProgrammedImpl g pk)
    (repairedSubmissionPrimeOracle g pk vote attacker)).run .empty

/-- The lowered source preserves the actual submission and final live cache in
law. This is a consequence of the stronger complete-state correspondence. -/
theorem repairedSubmissionPrimeSource_runtime (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2)) :
    𝒮[runBallotFiniteCache (repairedSubmissionPrimeSourceOracle g pk vote attacker) ∅] =
      𝒮[runBallotFiniteCache (repairedSubmissionFiniteSourceOracle g pk vote attacker) ∅] := by
  have h := evalSPMF_map_eq_of_evalSPMF_eq (repairedSubmissionPrime_runtime g pk vote attacker)
    (fun out => (out.1.1,out.2))
  simpa only [repairedSubmissionPrimeSourceOracle,repairedSubmissionFiniteSourceOracle,
    runBallotFiniteProgrammed,runBallotFiniteCache,simulateQ_map,StateT.run_map,
    Functor.map_map,Function.comp_def] using h

#print axioms drawPrimeNoncePair_finite_state
#print axioms repairedSubmissionWithNoncePairs_original
#print axioms repairedSubmissionPrime_runtime_bind
#print axioms repairedSubmissionPrime_runtime
#print axioms repairedSubmissionPrimeSource_runtime
end ExplainableCrypto.Helios.Computational
