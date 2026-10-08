import ExplainableCrypto.Helios.Computational.BallotReplayPath

/-! Project each proof trace from one shared original source path. Relabelling
leaves retains all query answers; no source rerun is used for a new selection. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
attribute [local implicit_reducible] ballotForkBudget PFunctor.FreeM.map
variable {F G A : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F]

private def mapPath {P : PFunctor.{0,0}} {α β : Type} (f : α → β) :
    (oa : PFunctor.FreeM P α) → PFunctor.FreeM.Path oa → PFunctor.FreeM.Path (PFunctor.FreeM.map f oa)
  | .pure _, _ => ⟨⟩
  | .liftBind _ next, ⟨answer,tail⟩ => ⟨answer,mapPath f (next answer) tail⟩

private theorem mapPath_output {P : PFunctor.{0,0}} {α β : Type} (f : α → β) :
    (oa : PFunctor.FreeM P α) → (path : PFunctor.FreeM.Path oa) →
    PFunctor.FreeM.output (PFunctor.FreeM.map f oa) (mapPath f oa path) = f (PFunctor.FreeM.output oa path)
  | .pure _, _ => rfl
  | .liftBind _ next, ⟨answer,tail⟩ => mapPath_output f (next answer) tail

private theorem mapPath_trace {P : PFunctor.{0,0}} {α β : Type} (f : α → β) :
    (oa : PFunctor.FreeM P α) → (path : PFunctor.FreeM.Path oa) →
    PFunctor.FreeM.Path.trace (PFunctor.FreeM.map f oa) (mapPath f oa path) =
      PFunctor.FreeM.Path.trace oa path
  | .pure _, _ => rfl
  | .liftBind t next, ⟨answer,tail⟩ =>
    by
      change ((⟨t,answer⟩ : Sigma P.B) :: _) = ((⟨t,answer⟩ : Sigma P.B) :: _)
      exact congrArg (List.cons ⟨t,answer⟩) (mapPath_trace f (next answer) tail)

private theorem mapPath_withPath {P : PFunctor.{0,0}} {α β : Type} (f : α → β) :
    (oa : PFunctor.FreeM P α) →
    PFunctor.FreeM.map (mapPath f oa) (PFunctor.FreeM.withPath oa) =
      PFunctor.FreeM.withPath (PFunctor.FreeM.map f oa)
  | .pure _ => rfl
  | .liftBind t next => by
    simp only [PFunctor.FreeM.withPath,PFunctor.FreeM.map]
    apply congrArg (PFunctor.FreeM.liftBind t)
    funext answer
    rw [← mapPath_withPath f (next answer),← PFunctor.FreeM.comp_map,
      ← PFunctor.FreeM.comp_map]
    rfl

abbrev ballotReplaySourceRun (oa : BallotOracleComp F G A) :=
  (simulateQ (ballotForkLoggedImpl (F := F) (G := G)) oa).run (∅,[])

def ballotReplaySourcePath (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G)
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun oa)) :
    PFunctor.FreeM.Path (ballotForkRunTrace (select <$> oa)) :=
  Eq.mpr (congrArg PFunctor.FreeM.Path (ballotForkRawSource_trace_eq oa select))
    (mapPath (ballotForkSourceTrace select) (ballotReplaySourceRun oa) path)

/-- Every selection reads the very same original source result and cache. -/
theorem ballotReplaySourcePath_output (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G)
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun oa)) :
    PFunctor.FreeM.output _ (ballotReplaySourcePath oa select path) =
      ballotForkSourceTrace select (PFunctor.FreeM.output _ path) := by
  have transport {P : PFunctor.{0,0}} {α : Type} (x y : PFunctor.FreeM P α)
      (he : x = y) (p : PFunctor.FreeM.Path y) :
      PFunctor.FreeM.output x (Eq.mpr (congrArg PFunctor.FreeM.Path he) p) =
        PFunctor.FreeM.output y p := by subst y; rfl
  unfold ballotReplaySourcePath
  exact (transport _ _ (ballotForkRawSource_trace_eq oa select) _).trans (mapPath_output _ _ path)

/-- The complete entropy-query trace is unchanged by proof selection. -/
theorem ballotReplaySourcePath_queries (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G)
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun oa)) :
    PFunctor.FreeM.Path.trace _ (ballotReplaySourcePath oa select path) =
      PFunctor.FreeM.Path.trace _ path := by
  have transport {P : PFunctor.{0,0}} {α : Type} (x y : PFunctor.FreeM P α)
      (he : x = y) (p : PFunctor.FreeM.Path y) :
      PFunctor.FreeM.Path.trace x (Eq.mpr (congrArg PFunctor.FreeM.Path he) p) =
        PFunctor.FreeM.Path.trace y p := by subst y; rfl
  unfold ballotReplaySourcePath
  exact (transport _ _ (ballotForkRawSource_trace_eq oa select) _).trans (mapPath_trace _ _ path)

/-- Selecting a trace after sampling the original path has exactly the same
path distribution as sampling that selected trace directly. -/
theorem ballotReplaySourcePath_distribution (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G) :
    ballotReplaySourcePath oa select <$> replayFirstPath (ballotReplaySourceRun oa) =
      replayFirstPath (ballotForkRunTrace (select <$> oa)) := by
  have transport {P : PFunctor.{0,0}} {α : Type} (x y : PFunctor.FreeM P α)
      (he : x = y) :
      PFunctor.FreeM.map (Eq.mpr (congrArg PFunctor.FreeM.Path he))
        (PFunctor.FreeM.withPath y) = PFunctor.FreeM.withPath x := by
    subst y
    exact PFunctor.FreeM.id_map _
  unfold ballotReplaySourcePath replayFirstPath
  change PFunctor.FreeM.map
    (Eq.mpr (congrArg PFunctor.FreeM.Path (ballotForkRawSource_trace_eq oa select)) ∘
      mapPath (ballotForkSourceTrace select) (ballotReplaySourceRun oa)) _ = _
  rw [PFunctor.FreeM.comp_map, mapPath_withPath]
  exact transport _ _ (ballotForkRawSource_trace_eq oa select)

def ballotReplaySourceAttempt (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G) (n : Nat)
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun oa)) :=
  Option.map (fun w => (ballotForkExtractPair w.outputs.1 w.outputs.2).2) <$>
    ballotReplayAtPath (select <$> oa) n (ballotReplaySourcePath oa select path)

/-- Each conditional attempt, averaged over the shared first execution, is
exactly the existing raw extractor with its statement projection erased. -/
theorem ballotReplaySourceAttempt_bind (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G) (n : Nat) :
    (do let path ← replayFirstPath (ballotReplaySourceRun oa)
        ballotReplaySourceAttempt oa select n path) =
      Option.map Prod.snd <$> ballotForkExtract (select <$> oa) n := by
  unfold ballotReplaySourceAttempt
  rw [← map_bind]
  have hb := bind_map_left (x := replayFirstPath (ballotReplaySourceRun oa))
    (f := ballotReplaySourcePath oa select) (g := ballotReplayAtPath (select <$> oa) n)
  rw [← hb,ballotReplaySourcePath_distribution,ballotReplayAtPath_bind]
  unfold ballotForkExtract contextFork
  change _ = Option.map Prod.snd <$> (Option.map _ <$>
    (Option.map PFunctor.FreeM.Cursor.SelectedForkView.outputs <$> _))
  simp only [Functor.map_map,Option.map_map,Function.comp_def]

section Probability
variable [Fintype F]
local instance replaySourceInhabited : Inhabited F := ⟨0⟩
noncomputable local instance replaySourceUniform : IsUniformSpec ((Unit →ₒ F) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

omit [AddCommGroup G] [Module F G] [DecidableEq F] in
/-- A typed original path yields an actual supported raw source execution. -/
theorem ballotReplaySourcePath_runtime_mem (oa : BallotOracleComp F G A)
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun oa)) :
    ((PFunctor.FreeM.output _ path).1,
      ballotForkCacheProject (PFunctor.FreeM.output _ path).2.1) ∈
      support (runBallotOracle oa ∅) := by
  have supportedOutput {ι : Type} {spec : OracleSpec.{0,0} ι} {α : Type}
      (m : OracleComp spec α) (p : PFunctor.FreeM.Path m) :
      PFunctor.FreeM.output m p ∈ support m := by
    have hp : PFunctor.FreeM.output m p ∈ support
        (PFunctor.FreeM.output m <$> replayFirstPath m) := by
      rw [support_map]
      exact Set.mem_image_of_mem _ (mem_support_replayFirstPath m p)
    rwa [map_output_replayFirstPath] at hp
  have hs := supportedOutput (ballotReplaySourceRun oa) path
  have hent := (mem_support_iff_of_evalSPMF_eq
    (ballotFork_entropy_eval (ballotReplaySourceRun oa)) _).mpr hs
  have hp : ((PFunctor.FreeM.output _ path).1,
      ballotForkCacheProject (PFunctor.FreeM.output _ path).2.1) ∈ support
      (Prod.map id (fun state => ballotForkCacheProject state.1) <$>
        simulateQ ballotForkEntropyImpl (ballotReplaySourceRun oa)) := by
    rw [support_map]
    exact Set.mem_image_of_mem _ hent
  unfold ballotReplaySourceRun at hp
  rw [ballotFork_runtime_eq] at hp
  exact hp

omit [AddCommGroup G] [Module F G] [DecidableEq F] in
/-- Forgetting the exact cache recovers the source membership interface. -/
theorem ballotReplaySourcePath_mem (oa : BallotOracleComp F G A)
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun oa)) :
    ∃ cache, ((PFunctor.FreeM.output _ path).1,cache) ∈ support (runBallotOracle oa ∅) :=
  ⟨_,ballotReplaySourcePath_runtime_mem oa path⟩

/-- Successful conditional replay extracts for this source execution's chosen
statement and unchanged full proof. No first-source correspondence premise. -/
theorem ballotReplaySourceAttempt_valid (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G) (n : Nat)
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun oa)) (wit : BallotWitness F)
    (ho : some wit ∈ support (ballotReplaySourceAttempt oa select n path)) :
    let target := select (PFunctor.FreeM.output _ path).1
    target.1.Witnesses wit ∧ ∃ c : F,
      target.2.Valid (fun _ => c) target.1.generator target.1.publicKey target.1.ciphertext := by
  rw [ballotReplaySourceAttempt,support_map] at ho
  obtain ⟨result,hr,he⟩ := ho
  cases result with
  | none => simp at he
  | some w =>
    have hrich := ballotReplayAtPath_supported _ n _ w hr
    have hp : some w.outputs ∈ support (contextFork (ballotForkRunTrace (select <$> oa))
        (ballotForkBudget (F := F) n) (.inr ()) (ballotForkSelector n)) := by
      unfold contextFork
      change some w.outputs ∈ support (Option.map PFunctor.FreeM.Cursor.SelectedForkView.outputs <$> _)
      rw [support_map]
      exact ⟨some w,hrich,rfl⟩
    have hv := ballotFork_pair_extract_valid _ n w.outputs.1 w.outputs.2 hp
    have hfirst := ballotReplayAtPath_first _ n _ w hr
    have ht : w.outputs.1 = ballotForkSourceTrace select (PFunctor.FreeM.output _ path) := by
      change PFunctor.FreeM.output _ w.view.firstPath = _
      rw [hfirst,ballotReplaySourcePath_output]
    have hw := contextForkWitness_success _ _ _ _ hrich
    have hpath := replayPathResult_mem_support_replayFirstRun _ w.view.firstPath
      (mem_support_replayFirstPath _ _)
    obtain ⟨c,_,_,hvalid⟩ := ballotFork_selected_challenge _ n w.outputs.1
      (PFunctor.FreeM.Path.trace _ w.view.firstPath) hpath w.label hw.2.2.1
    have hwit : (ballotForkExtractPair w.outputs.1 w.outputs.2).2 = wit :=
      Option.some.inj he
    rw [hwit] at hv
    rw [ht] at hv hvalid
    exact ⟨hv,c,hvalid⟩
end Probability

#print axioms ballotReplaySourcePath_distribution
#print axioms ballotReplaySourceAttempt_bind
#print axioms ballotReplaySourcePath_runtime_mem
#print axioms ballotReplaySourcePath_mem
#print axioms ballotReplaySourcePath_output
#print axioms ballotReplaySourcePath_queries
#print axioms ballotReplaySourceAttempt_valid
end ExplainableCrypto.Helios.Computational
