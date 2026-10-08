import ExplainableCrypto.Helios.Computational.ElectionAcceptance
import ExplainableCrypto.Helios.Computational.ElectionQueryBound
import ExplainableCrypto.Helios.Computational.BallotJointReplayBound

/-! Relate full-election acceptance to simultaneous original replay selection,
then instantiate the existing joint lower bound. Honest-proof simulation for
DDH reduction and standard-PPT costs remain separate obligations. -/
namespace ExplainableCrypto.Helios.Computational.ElectionExtractionBound
open OracleComp OracleSpec ElectionOracle ElectionExtraction ElectionQueryBound
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]
local instance : Inhabited F := ⟨0⟩
noncomputable local instance : IsUniformSpec ((Unit →ₒ F) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

private theorem trace_verified {Init State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (hg : g ≠ 0) (prepare : Comp F G Init) (adversary : Init → Adversary F G State)
    (raw : (PublicResult F G × Bool) × FiatShamir.Fork.SimState Unit (BallotForkPoint G) F)
    (hraw : (raw.1,ballotForkCacheProject raw.2.1) ∈ support (runBallotOracle
      (ElectionReplaySource.source (preparedSource fingerprint g prepare adversary)) ∅))
    (i : Option (Fin 2)) :
    (ballotForkSourceTrace (select g i) raw).verified = decide (raw.1.1.decision = .accepted) := by
  by_cases ha : raw.1.1.decision = .accepted
  · obtain ⟨c,hcache,hvalid⟩ := ElectionAcceptance.source_cached fingerprint g prepare adversary
      (raw.1,ballotForkCacheProject raw.2.1) hraw ha i
    have hkey : raw.2.1 ((),(select g i raw.1).1,(select g i raw.1).2.commitment) = some c := by
      simp only [select]
      rw [if_pos ha]
      exact hcache
    rw [show decide (raw.1.1.decision = .accepted) = true from decide_eq_true ha]
    dsimp only [ballotForkSourceTrace]
    rw [hkey]
    dsimp only
    simp only [decide_eq_true_eq]
    exact ⟨True.intro,by simpa [select,ha,Ballot.coveredStatement] using hvalid⟩
  · rw [show decide (raw.1.1.decision = .accepted) = false from decide_eq_false ha]
    dsimp only [ballotForkSourceTrace]
    split
    · rfl
    · simp only [decide_eq_false_iff_not]
      rintro ⟨_,hp⟩
      simp only [select,if_neg ha,Ballot.coveredStatement] at hp
      exact hg (by simpa [replayRejectedProof,Branch.Valid] using hp.1.1.symm)

/-- Each selected trace verifies exactly on acceptance of that same complete
original election path. All final-cache evidence is derived from execution. -/
theorem path_verified {Init State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (hg : g ≠ 0) (prepare : Comp F G Init) (adversary : Init → Adversary F G State)
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun
      (ElectionReplaySource.source (preparedSource fingerprint g prepare adversary))))
    (i : Option (Fin 2)) :
    (PFunctor.FreeM.output _ (ballotReplaySourcePath _ (select g i) path)).verified =
      decide ((PFunctor.FreeM.output _ path).1.1.decision = .accepted) := by
  exact (congrArg (fun t : BallotForkTrace F G => t.verified)
    (ballotReplaySourcePath_output _ (select g i) path)).trans
      (trace_verified fingerprint g hg prepare adversary _ (ballotReplaySourcePath_runtime_mem _ path) i)

/-- Callback budgets and the actual 15-query protocol bound enable all three
selectors exactly on accepted full-election paths. This does not assume selection. -/
theorem path_selector {Init State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (hg : g ≠ 0) (prepare : Comp F G Init) (adversary : Init → Adversary F G State)
    (np nc ng : Nat) (hp : prepare.IsQueryBoundP (isBallot (F := F)) np)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsQueryBoundP (isBallot (F := F)) nc)
    (hh : ∀ initial saved view, ((adversary initial).guessVote saved view).IsQueryBoundP (isBallot (F := F)) ng)
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun
      (ElectionReplaySource.source (preparedSource fingerprint g prepare adversary))))
    (i : Option (Fin 2)) :
    (ballotForkSelector (np+nc+ng+15) (PFunctor.FreeM.output _
      (ballotReplaySourcePath _ (select g i) path))).isSome =
      decide ((PFunctor.FreeM.output _ path).1.1.decision = .accepted) := by
  have hb := source_bound _ _ (prepared_bound fingerprint g prepare adversary np nc ng hp hc hh)
  have hbudget : (select g i <$> ElectionReplaySource.source
      (preparedSource fingerprint g prepare adversary)).IsQueryBoundP
      (isBallotHashQuery (F := F)) (np+nc+ng+15+1) := by
    rw [isQueryBoundP_map_iff]
    exact hb.mono (by omega)
  have supportedOutput {ι : Type} {spec : OracleSpec.{0,0} ι} {A : Type}
      (m : OracleComp spec A) (p : PFunctor.FreeM.Path m) :
      PFunctor.FreeM.output m p ∈ support m := by
    have hp : PFunctor.FreeM.output m p ∈ support
        (PFunctor.FreeM.output m <$> replayFirstPath m) := by
      rw [support_map]
      exact Set.mem_image_of_mem _ (mem_support_replayFirstPath m p)
    rwa [map_output_replayFirstPath] at hp
  rw [ballotFork_selector_of_bound _ (np+nc+ng+15) hbudget _ (supportedOutput _ _)]
  exact path_verified fingerprint g hg prepare adversary path i

/-- Simultaneous original selection has exactly the actual complete-election
submission-acceptance probability, including preparation and final queries. -/
theorem selection_probability {Init State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (hg : g ≠ 0) (prepare : Comp F G Init) (adversary : Init → Adversary F G State)
    (np nc ng : Nat) (hp : prepare.IsQueryBoundP (isBallot (F := F)) np)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsQueryBoundP (isBallot (F := F)) nc)
    (hh : ∀ initial saved view, ((adversary initial).guessVote saved view).IsQueryBoundP (isBallot (F := F)) ng) :
    Pr[fun path => ∀ i : Option (Fin 2),
      (ballotForkSelector (np+nc+ng+15) (PFunctor.FreeM.output _
        (ballotReplaySourcePath _ (select g i) path))).isSome |
      replayFirstPath (ballotReplaySourceRun
        (ElectionReplaySource.source (preparedSource fingerprint g prepare adversary)))] =
    Pr[fun out => out.1.1.decision = .accepted |
      run (preparedSource fingerprint g prepare adversary) (fun _ => none)] := by
  let source := ElectionReplaySource.source (preparedSource fingerprint g prepare adversary)
  have hsource : Pr[fun raw => raw.1.1.decision = .accepted | ballotReplaySourceRun source] =
      Pr[fun out => out.1.1.decision = .accepted |
        run (preparedSource fingerprint g prepare adversary) (fun _ => none)] := by
    calc
      _ = Pr[fun raw => raw.1.1.decision = .accepted |
          simulateQ ballotForkEntropyImpl (ballotReplaySourceRun source)] :=
        (probEvent_congr' (fun _ _ => Iff.rfl) (ballotFork_entropy_eval _)).symm
      _ = Pr[fun out => out.1.1.decision = .accepted | runBallotOracle source ∅] := by
        have h := congrArg (fun m => Pr[fun out => out.1.1.decision = .accepted | m])
          (ballotFork_runtime_eq source (∅,[]))
        have he : ballotForkCacheProject (∅ : (Unit × BallotForkPoint G →ₒ F).QueryCache) =
            (∅ : BallotOracleCache F G) := by funext key; rfl
        simpa only [he,probEvent_map,Function.comp_def,Prod.map,id_eq,ballotReplaySourceRun] using h
      _ = _ := by
        have h := congrArg (fun m => Pr[fun out => out.1.decision = .accepted | m])
          (ElectionReplaySource.source_runtime (preparedSource fingerprint g prepare adversary))
        simpa only [probEvent_map,Function.comp_def,source] using h
  calc
    _ = Pr[fun path => (PFunctor.FreeM.output _ path).1.1.decision = .accepted |
        replayFirstPath (ballotReplaySourceRun source)] := by
      apply probEvent_congr' _ rfl
      intro path _
      simp only [path_selector fingerprint g hg prepare adversary np nc ng hp hc hh path,
        decide_eq_true_eq,forall_const]
      rfl
    _ = Pr[fun raw => raw.1.1.decision = .accepted | ballotReplaySourceRun source] := by
      have h := congrArg (fun m => Pr[fun raw => raw.1.1.decision = .accepted | m])
        (map_output_replayFirstPath (ballotReplaySourceRun source))
      simpa only [probEvent_map,Function.comp_def] using h
    _ = _ := hsource

/-- The existing joint replay bound now uses actual full-election acceptance,
with a derived protocol/query budget and no assumed source or selector invariant. -/
theorem joint_le {Init State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (hg : g ≠ 0) (prepare : Comp F G Init) (adversary : Init → Adversary F G State)
    (np nc ng : Nat) (hp : prepare.IsQueryBoundP (isBallot (F := F)) np)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsQueryBoundP (isBallot (F := F)) nc)
    (hh : ∀ initial saved view, ((adversary initial).guessVote saved view).IsQueryBoundP (isBallot (F := F)) ng)
    (δ : ENNReal) :
    let a := Pr[fun out => out.1.1.decision = .accepted |
      run (preparedSource fingerprint g prepare adversary) (fun _ => none)]
    (a - 3*(np+nc+ng+16 : ENNReal)*δ) * (δ - (Fintype.card F : ENNReal)⁻¹)^3 ≤
      Pr[fun out => out.isSome | joint fingerprint g prepare adversary (np+nc+ng+15)] := by
  have h := ballotJointReplay_selection_le
    (ElectionReplaySource.source (preparedSource fingerprint g prepare adversary))
    (select g) (np+nc+ng+15) δ
  dsimp only at h ⊢
  rw [selection_probability fingerprint g hg prepare adversary np nc ng hp hc hh] at h
  simpa only [joint,ElectionReplaySource.jointExtract,Nat.cast_add,Nat.cast_ofNat,
    add_assoc,show (15 : ENNReal)+1=16 by norm_num] using h

#print axioms path_verified
#print axioms path_selector
#print axioms selection_probability
#print axioms joint_le
end ExplainableCrypto.Helios.Computational.ElectionExtractionBound
