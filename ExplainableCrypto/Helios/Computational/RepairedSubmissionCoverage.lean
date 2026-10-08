import ExplainableCrypto.Helios.Computational.RepairedSubmissionJoint

/-! Actual accepted source paths have live bounded replay selectors for all
three covered proofs. The original path's cache is retained in the argument;
no per-selection completion or assumed cache correspondence is introduced. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F] [Fintype F]
local instance coverageInhabited : Inhabited F := ⟨0⟩
noncomputable local instance coverageUniform : IsUniformSpec ((Unit →ₒ F) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

attribute [local irreducible] repairedSubmissionSourceOracle
attribute [local implicit_reducible] ballotForkBudget

omit [Fintype F] in
private theorem cached_of_verify_eq (stmt : BallotStatement G) (p : Proof01 F G)
    (cache : BallotOracleCache F G)
    (h : runBallotOracle (strongBallotVerifyOracle stmt p) cache = pure (true,cache)) :
    ∃ c : F, cache (stmt,p.commitment) = some c ∧
      p.Valid (fun _ => c) stmt.generator stmt.publicKey stmt.ciphertext := by
  have hs : (true,cache) ∈ support (runBallotOracle (strongBallotVerifyOracle stmt p) cache) := by
    rw [h]; simp
  exact runBallotOracle_verify_true_cached stmt p cache (true,cache) hs rfl

omit [SampleableType F] [Fintype F] in
private theorem trace_verified (g pk : G) (hg : g ≠ 0)
    (raw : RepairedSubmissionResult F G × FiatShamir.Fork.SimState Unit (BallotForkPoint G) F)
    (i : Option (Fin 2))
    (hv : raw.1.Accepted → ∃ c : F,
      raw.2.1 ((),raw.1.ballot.coveredStatement g pk i,(raw.1.ballot.coveredProof i).commitment) = some c ∧
      (raw.1.ballot.coveredProof i).Valid (fun _ => c) g pk (raw.1.ballot.coveredCiphertext i)) :
    (ballotForkSourceTrace (repairedSubmissionSelect g pk i) raw).verified = decide raw.1.Accepted := by
  by_cases ha : raw.1.Accepted
  · obtain ⟨c,hcache,hvalid⟩ := hv ha
    have hkey : raw.2.1 ((),(repairedSubmissionSelect g pk i raw.1).1,
        (repairedSubmissionSelect g pk i raw.1).2.commitment) = some c := by
      simp only [repairedSubmissionSelect]
      rw [if_pos ha]
      exact hcache
    rw [show decide raw.1.Accepted = true from decide_eq_true ha]
    dsimp only [ballotForkSourceTrace]
    rw [hkey]
    dsimp only
    simp only [decide_eq_true_eq]
    exact ⟨True.intro,by simpa [repairedSubmissionSelect,ha,Ballot.coveredStatement] using hvalid⟩
  · rw [show decide raw.1.Accepted = false from decide_eq_false ha]
    dsimp only [ballotForkSourceTrace]
    split
    · rfl
    · simp only [decide_eq_false_iff_not]
      rintro ⟨_,hp⟩
      simp [repairedSubmissionSelect,ha,Ballot.coveredStatement] at hp
      exact hg (by simpa [replayRejectedProof,Branch.Valid] using hp.1.1.symm)

theorem repairedSubmissionSource_trace_verified (g pk : G) (hg : g ≠ 0) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2))
    (raw : RepairedSubmissionResult F G × FiatShamir.Fork.SimState Unit (BallotForkPoint G) F)
    (hraw : (raw.1,ballotForkCacheProject raw.2.1) ∈ support
      (runBallotOracle (repairedSubmissionSourceOracle g pk vote attacker) ∅))
    (i : Option (Fin 2)) :
    (ballotForkSourceTrace (repairedSubmissionSelect g pk i) raw).verified = decide raw.1.Accepted := by
  apply trace_verified g pk hg raw i
  intro ha
  rw [repairedSubmissionSource_runtime,support_map] at hraw
  obtain ⟨out,hout,he⟩ := hraw
  have hr : out.1.1 = raw.1 := congrArg Prod.fst he
  have hc : out.2 = ballotForkCacheProject raw.2.1 := congrArg Prod.snd he
  have hao : out.1.1.Accepted := hr ▸ ha
  have hv := repairedSubmissionOracle_accepted_live g pk vote attacker out hout hao.1 hao.2 i
  obtain ⟨c,hcache,hvalid⟩ := cached_of_verify_eq _ _ _ hv
  rw [hr,hc] at hcache
  rw [hr] at hvalid
  exact ⟨c,hcache,hvalid⟩

/-- A projected trace's original full proof is live-valid exactly on joint
acceptance of this same source path. All cache evidence is derived. -/
theorem repairedSubmissionPath_verified (g pk : G) (hg : g ≠ 0) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2))
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun
      (repairedSubmissionSourceOracle g pk vote attacker))) (i : Option (Fin 2)) :
    (PFunctor.FreeM.output _ (ballotReplaySourcePath _ (repairedSubmissionSelect g pk i) path)).verified =
      decide (PFunctor.FreeM.output _ path).1.Accepted := by
  exact (congrArg (fun t : BallotForkTrace F G => t.verified)
    (ballotReplaySourcePath_output _ (repairedSubmissionSelect g pk i) path)).trans
      (repairedSubmissionSource_trace_verified g pk hg vote attacker _ (ballotReplaySourcePath_runtime_mem _ path) i)

/-- The source query bound and derived empty-runtime cache/log invariant cover
all three selected live queries, on exactly the accepting original paths. -/
theorem repairedSubmissionPath_selector (g pk : G) (hg : g ≠ 0) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (n : Nat)
    (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := F)) n)
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun
      (repairedSubmissionSourceOracle g pk vote attacker))) (i : Option (Fin 2)) :
    (ballotForkSelector (n+15) (PFunctor.FreeM.output _
      (ballotReplaySourcePath _ (repairedSubmissionSelect g pk i) path))).isSome =
      decide (PFunctor.FreeM.output _ path).1.Accepted := by
  have hbudget : (repairedSubmissionSelect g pk i <$>
      repairedSubmissionSourceOracle g pk vote attacker).IsQueryBoundP
        (isBallotHashQuery (F := F)) (n+15+1) := by
    rw [repairedSubmissionSource_select_eq]
    exact (repairedSubmissionTargetOracle_query_bound g pk vote attacker i n hb).mono (by omega)
  have supportedOutput {ι : Type} {spec : OracleSpec.{0,0} ι} {α : Type}
      (m : OracleComp spec α) (p : PFunctor.FreeM.Path m) :
      PFunctor.FreeM.output m p ∈ support m := by
    have hp : PFunctor.FreeM.output m p ∈ support
        (PFunctor.FreeM.output m <$> replayFirstPath m) := by
      rw [support_map]
      exact Set.mem_image_of_mem _ (mem_support_replayFirstPath m p)
    rwa [map_output_replayFirstPath] at hp
  rw [ballotFork_selector_of_bound _ (n+15) hbudget _ (supportedOutput _ _)]
  exact repairedSubmissionPath_verified g pk hg vote attacker path i

/-- Each accepted path supplies a physical replay occurrence for every covered
proof. The locations are derived from the existing path reachability theorem. -/
theorem repairedSubmissionPath_locations (g pk : G) (hg : g ≠ 0) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (n : Nat)
    (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := F)) n)
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun
      (repairedSubmissionSourceOracle g pk vote attacker)))
    (ha : (PFunctor.FreeM.output _ path).1.Accepted) (i : Option (Fin 2)) :
    let oa := repairedSubmissionSelect g pk i <$> repairedSubmissionSourceOracle g pk vote attacker
    let selected := ballotReplaySourcePath _ (repairedSubmissionSelect g pk i) path
    ∃ s : Fin (n+15+1), ballotForkSelector (n+15) (PFunctor.FreeM.output _ selected) = some s ∧
      (PFunctor.FreeM.Cursor.locateAt? (P := (FiatShamir.Fork.wrappedSpec F).toPFunctor)
        (Sum.inr ()) (ballotForkRunTrace oa) selected s).isSome := by
  dsimp only
  have hs := repairedSubmissionPath_selector g pk hg vote attacker n hb path i
  rw [show decide (PFunctor.FreeM.output _ path).1.Accepted = true from decide_eq_true ha] at hs
  cases he : ballotForkSelector (n+15) (PFunctor.FreeM.output _
      (ballotReplaySourcePath _ (repairedSubmissionSelect g pk i) path)) with
  | none => simp [he] at hs
  | some s =>
    refine ⟨s,rfl,?_⟩
    exact CfReachable.toPathCfReachable (ballotFork_selector_reachable _ (n+15)) _ s he

/-- All three selectors are enabled together with probability exactly equal
to actual joint submission acceptance. This is not joint replay success. -/
theorem repairedSubmissionPath_selection_probability (g pk : G) (hg : g ≠ 0) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (n : Nat)
    (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := F)) n) :
    Pr[fun path => ∀ i : Option (Fin 2),
      (ballotForkSelector (n+15) (PFunctor.FreeM.output _
        (ballotReplaySourcePath _ (repairedSubmissionSelect g pk i) path))).isSome |
      replayFirstPath (ballotReplaySourceRun (repairedSubmissionSourceOracle g pk vote attacker))] =
    Pr[fun out => out.1.1.Accepted |
      runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker)] := by
  let source := repairedSubmissionSourceOracle g pk vote attacker
  have hsource : Pr[fun raw => raw.1.Accepted | ballotReplaySourceRun source] =
      Pr[fun out => out.1.1.Accepted |
        runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker)] := by
    calc
      _ = Pr[fun raw => raw.1.Accepted |
          simulateQ ballotForkEntropyImpl (ballotReplaySourceRun source)] :=
        (probEvent_congr' (fun _ _ => Iff.rfl) (ballotFork_entropy_eval _)).symm
      _ = Pr[fun out => out.1.Accepted | runBallotOracle source ∅] := by
        have h := congrArg (fun m => Pr[fun out => out.1.Accepted | m])
          (ballotFork_runtime_eq source (∅,[]))
        have hempty : ballotForkCacheProject (∅ : (Unit × BallotForkPoint G →ₒ F).QueryCache) =
            (∅ : BallotOracleCache F G) := by funext key; rfl
        simpa only [hempty,probEvent_map,Function.comp_def,Prod.map,id_eq,ballotReplaySourceRun] using h
      _ = _ := by dsimp only [source]; rw [repairedSubmissionSource_runtime,probEvent_map]; rfl
  calc
    _ = Pr[fun path => (PFunctor.FreeM.output _ path).1.Accepted |
        replayFirstPath (ballotReplaySourceRun source)] := by
      apply probEvent_congr' _ rfl
      intro path _
      simp only [repairedSubmissionPath_selector g pk hg vote attacker n hb path,
        decide_eq_true_eq,forall_const]
      rfl
    _ = Pr[fun raw => raw.1.Accepted | ballotReplaySourceRun source] := by
      have h := congrArg (fun m => Pr[fun raw => raw.1.Accepted | m])
        (map_output_replayFirstPath (ballotReplaySourceRun source))
      simpa only [probEvent_map,Function.comp_def] using h
    _ = _ := hsource

#print axioms repairedSubmissionSource_trace_verified
#print axioms repairedSubmissionPath_locations
#print axioms repairedSubmissionPath_selection_probability
#print axioms repairedSubmissionPath_verified
#print axioms repairedSubmissionPath_selector
end ExplainableCrypto.Helios.Computational
