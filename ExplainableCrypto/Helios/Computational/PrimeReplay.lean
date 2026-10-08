import ExplainableCrypto.Helios.Computational.PrimeSubmission
import ExplainableCrypto.Helios.Computational.RepairedSubmissionJointBound
import ExplainableCrypto.Helios.Computational.ReplayBitsExecution

/-! Reapply generic three-proof replay to the explicit source itself. Runtime-law
transport is used for cached validity, never as a replay-path correspondence. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {q : Nat} [Fact q.Prime] {G : Type} [AddCommGroup G]
  [Module (ZMod q) G] [DecidableEq G]
local instance primeReplayInhabited : Inhabited (ZMod q) := ⟨0⟩
noncomputable local instance primeReplayUniform : IsUniformSpec ((Unit →ₒ ZMod q) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _
attribute [local irreducible] repairedSubmissionPrimeSourceOracle repairedSubmissionSourceOracle
attribute [local implicit_reducible] ballotForkBudget
attribute [local irreducible] drawPrimeNoncePair strongHonestBallotWithNoncesOracle repairedSubmitOracle

/-- The exact cache projection turns full finite source correspondence into the
semantic runtime law needed to check cached proofs on the new source's paths. -/
theorem repairedSubmissionPrimeSource_semantic_runtime (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2)) :
    𝒮[runBallotOracle (repairedSubmissionPrimeSourceOracle g pk vote attacker) ∅] =
      𝒮[runBallotOracle (repairedSubmissionSourceOracle g pk vote attacker) ∅] := by
  have h := evalSPMF_map_eq_of_evalSPMF_eq (repairedSubmissionPrimeSource_runtime g pk vote attacker)
    (fun out => (out.1,out.2.denote))
  simpa only [runBallotFiniteCache_eq,BallotFiniteCache.denote_empty,
    repairedSubmissionFiniteSource_eq] using h

/-- Derive the budget from the new source syntax; equality of distributions
alone would not imply a syntactic query bound. -/
theorem repairedSubmissionPrimeOracle_query_bound (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2))
    (n : Nat) (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n) :
    (repairedSubmissionPrimeOracle g pk vote attacker).IsQueryBoundP growsBallotCache (n+15) := by
  have hn := honestUniform_query_bound (F := ZMod q) (G := G) (drawPrimeNoncePair (q := q))
    growsBallotCache (by simp [growsBallotCache])
  have hp (v : Bool) (rs : ZMod q × ZMod q) :
      (strongHonestBallotWithNoncesOracle g pk v rs).IsQueryBoundP growsBallotCache 3 := by
    simp [strongHonestBallotWithNoncesOracle,ballotProofQuery,growsBallotCache]
  unfold repairedSubmissionPrimeOracle repairedSubmissionWithNoncePairs
  rw [← Nat.zero_add (n+15)]
  apply isQueryBoundP_bind (n := 0) (m := n+15) hn
  intro rs0 _
  rw [show n+15 = 3+(3+(0+(3+(3+(n+3))))) by omega]
  apply isQueryBoundP_bind (n := 3) (m := 3+(0+(3+(3+(n+3))))) (hp vote rs0)
  intro alice _
  apply isQueryBoundP_bind (n := 3) (m := 0+(3+(3+(n+3))))
    (repairedSubmitOracle_query_bounds g pk 0 [] alice).1
  intro first _
  apply isQueryBoundP_bind (n := 0) (m := 3+(3+(n+3))) hn
  intro rs1 _
  apply isQueryBoundP_bind (n := 3) (m := 3+(n+3)) (hp (!vote) rs1)
  intro bob _
  apply isQueryBoundP_bind (n := 3) (m := n+3)
    (repairedSubmitOracle_query_bounds g pk 1 first.2 bob).1
  intro second _
  dsimp only
  apply isQueryBoundP_bind (n := n) (m := 3) (raw_lift_hash_bound _ n (hb _))
  intro ballot _
  apply isQueryBoundP_bind (n := 3) (m := 0) (repairedSubmitOracle_query_bounds g pk 2 second.2 ballot).1
  simp

/-- Lowering through the actual finite handler derives the raw n+15 hash bound. -/
theorem repairedSubmissionPrimeSource_query_bound (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2))
    (n : Nat) (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n) :
    (repairedSubmissionPrimeSourceOracle g pk vote attacker).IsQueryBoundP
      (isBallotHashQuery (F := ZMod q)) (n+15) := by
  have h := ballotProgrammed_query_bound g pk _ (n+15)
    (repairedSubmissionPrimeOracle_query_bound g pk vote attacker n hb) .empty
  have he := runBallotFiniteProgrammed_eq g pk (repairedSubmissionPrimeOracle g pk vote attacker) .empty
  rw [BallotFiniteProgrammedState.denote_empty] at he
  rw [← he] at h
  simp only [isQueryBoundP_map_iff] at h
  simpa only [repairedSubmissionPrimeSourceOracle,isQueryBoundP_map_iff] using h

/-- Cache validity is transported from an actual supported runtime, then applied
to this source's own path. No old path is invented or assumed to correspond. -/
theorem repairedSubmissionPrimePath_verified (g pk : G) (hg : g ≠ 0) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2))
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun (repairedSubmissionPrimeSourceOracle g pk vote attacker)))
    (i : Option (Fin 2)) :
    (PFunctor.FreeM.output _ (ballotReplaySourcePath _ (repairedSubmissionSelect g pk i) path)).verified =
      decide (PFunctor.FreeM.output _ path).1.Accepted := by
  have hm := ballotReplaySourcePath_runtime_mem _ path
  have hold := (mem_support_iff_of_evalSPMF_eq
    (repairedSubmissionPrimeSource_semantic_runtime g pk vote attacker) _).mp hm
  exact (congrArg (fun t : BallotForkTrace (ZMod q) G => t.verified)
    (ballotReplaySourcePath_output _ (repairedSubmissionSelect g pk i) path)).trans
      (repairedSubmissionSource_trace_verified g pk hg vote attacker _ hold i)

/-- All selected queries on the explicit source's own paths are enabled exactly
on joint acceptance, with their budget derived from that source. -/
theorem repairedSubmissionPrimePath_selector (g pk : G) (hg : g ≠ 0) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2))
    (n : Nat) (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n)
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun (repairedSubmissionPrimeSourceOracle g pk vote attacker)))
    (i : Option (Fin 2)) :
    (ballotForkSelector (n+15) (PFunctor.FreeM.output _
      (ballotReplaySourcePath _ (repairedSubmissionSelect g pk i) path))).isSome =
      decide (PFunctor.FreeM.output _ path).1.Accepted := by
  have hb' : (repairedSubmissionSelect g pk i <$>
      repairedSubmissionPrimeSourceOracle g pk vote attacker).IsQueryBoundP
        (isBallotHashQuery (F := ZMod q)) (n+15+1) := by
    rw [isQueryBoundP_map_iff]
    exact (repairedSubmissionPrimeSource_query_bound g pk vote attacker n hb).mono (by omega)
  have hout : PFunctor.FreeM.output _ (ballotReplaySourcePath _ (repairedSubmissionSelect g pk i) path)
      ∈ support (ballotForkRunTrace (repairedSubmissionSelect g pk i <$>
        repairedSubmissionPrimeSourceOracle g pk vote attacker)) := by
    have h := Set.mem_image_of_mem (PFunctor.FreeM.output _)
      (mem_support_replayFirstPath _ (ballotReplaySourcePath _ (repairedSubmissionSelect g pk i) path))
    rw [← support_map,map_output_replayFirstPath] at h
    exact h
  rw [ballotFork_selector_of_bound _ (n+15) hb' _ hout]
  exact repairedSubmissionPrimePath_verified g pk hg vote attacker path i

#print axioms repairedSubmissionPrimeSource_semantic_runtime
#print axioms repairedSubmissionPrimeOracle_query_bound
#print axioms repairedSubmissionPrimeSource_query_bound
#print axioms repairedSubmissionPrimePath_verified
#print axioms repairedSubmissionPrimePath_selector
end ExplainableCrypto.Helios.Computational
