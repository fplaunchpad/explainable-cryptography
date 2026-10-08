import ExplainableCrypto.Helios.Computational.BallotForkAcceptance

/-! Retain the first source output using VCVio's existing rich fork witness.
Only the leaf projection is inverted along its typed path. Hash keys, replay
queries and the full-proof verifier are those of the existing extractor. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G A : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F]

local instance sourceProofValidityDecidable (p : Proof01 F G) (c : F) (stmt : BallotStatement G) :
    Decidable (p.Valid (fun _ => c) stmt.generator stmt.publicKey stmt.ciphertext) := by
  unfold Proof01.Valid Branch.Valid; infer_instance

/-- Append the existing verifier query, retaining the original source value. -/
def ballotForkSourceComplete (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G) : BallotOracleComp F G A := do
  let a ← oa
  let _ ← ballotChallengeOracle (select a).1 (select a).2.commitment
  pure a

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] [SampleableType F] in
theorem ballotForkSourceComplete_project (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G) :
    select <$> ballotForkSourceComplete oa select = ballotForkComplete (select <$> oa) := by
  simp [ballotForkSourceComplete,ballotForkComplete,map_bind]

def ballotForkSourceRun (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G) :=
  (simulateQ (ballotForkLoggedImpl (F := F) (G := G))
    (ballotForkSourceComplete oa select)).run (∅,[])

def ballotForkSourceTrace (select : A → BallotStatement G × Proof01 F G)
    (out : A × FiatShamir.Fork.SimState Unit (BallotForkPoint G) F) : BallotForkTrace F G :=
  let p := select out.1
  { forgery := ((),(p.1,p.2.commitment),p.2)
    advCache := ∅
    roCache := out.2.1
    queryLog := out.2.2
    verified := match out.2.1 ((),p.1,p.2.commitment) with
      | none => false
      | some c => decide (p.2.commitment = p.2.commitment ∧
          p.2.Valid (fun _ => c) p.1.generator p.1.publicKey p.1.ciphertext) }

/-- Every proof selection is a pure leaf projection of one logged source run.
This version adds no completion query and is used to share a first path. -/
theorem ballotForkRawSource_trace_eq (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G) :
    ballotForkRunTrace (select <$> oa) = ballotForkSourceTrace select <$>
      (simulateQ (ballotForkLoggedImpl (F := F) (G := G)) oa).run (∅,[]) := by
  rw [ballotForkRunTrace_eq]
  unfold ballotForkSourceTrace
  simp only [simulateQ_map,StateT.run_map,bind_pure_comp]
  rw [Functor.map_map]
  rfl

/-- Exact equality of query trees, not merely equality of output distributions. -/
theorem ballotForkSource_trace_eq (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G) :
    ballotForkRunTrace (ballotForkComplete (select <$> oa)) =
      ballotForkSourceTrace select <$> ballotForkSourceRun oa select := by
  rw [← ballotForkSourceComplete_project]
  exact ballotForkRawSource_trace_eq _ select

private theorem output_pullMap {ι : Type} {spec : OracleSpec.{0,0} ι} {α β : Type}
    (f : α → β) (oa : OracleComp spec α)
    (path : PFunctor.FreeM.Path (f <$> oa)) :
    f (PFunctor.FreeM.output oa (PFunctor.FreeM.Path.pullMap f oa path)) =
      PFunctor.FreeM.output (f <$> oa) path := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t next ih =>
    rcases path with ⟨answer,tail⟩
    exact ih answer tail

/-- Recover the actual first source output from the existing fork's first path. -/
def ballotForkSourceFirst (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G)
    (path : PFunctor.FreeM.Path (ballotForkRunTrace (ballotForkComplete (select <$> oa)))) :=
  PFunctor.FreeM.output (ballotForkSourceRun oa select)
    (PFunctor.FreeM.Path.pullMap (ballotForkSourceTrace select) (ballotForkSourceRun oa select)
      (Eq.mp (congrArg PFunctor.FreeM.Path (ballotForkSource_trace_eq oa select)) path))

theorem ballotForkSourceFirst_trace (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G)
    (path : PFunctor.FreeM.Path (ballotForkRunTrace (ballotForkComplete (select <$> oa)))) :
    ballotForkSourceTrace select (ballotForkSourceFirst oa select path) =
      PFunctor.FreeM.output (ballotForkRunTrace (ballotForkComplete (select <$> oa))) path := by
  unfold ballotForkSourceFirst
  have h := output_pullMap (ballotForkSourceTrace select) (ballotForkSourceRun oa select)
    (Eq.mp (congrArg PFunctor.FreeM.Path (ballotForkSource_trace_eq oa select)) path)
  have transport {ι : Type} {spec : OracleSpec.{0,0} ι} {α : Type}
      (x y : OracleComp spec α) (he : x = y) (p : PFunctor.FreeM.Path x) :
      PFunctor.FreeM.output y (Eq.mp (congrArg PFunctor.FreeM.Path he) p) =
        PFunctor.FreeM.output x p := by subst y; rfl
  exact h.trans (transport _ _ (ballotForkSource_trace_eq oa select) path)

def ballotForkSourceExtract (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G) (n : Nat) :=
  Option.map (fun w =>
    ((ballotForkSourceFirst oa select w.view.firstPath).1,
      ballotForkExtractPair w.outputs.1 w.outputs.2)) <$>
    contextForkWitness (ballotForkRunTrace (ballotForkComplete (select <$> oa)))
      (ballotForkBudget (F := F) n) (.inr ()) (ballotForkSelector n)

/-- Dropping the retained source value reproduces the existing extractor exactly. -/
theorem ballotForkSourceExtract_project (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G) (n : Nat) :
    Option.map Prod.snd <$> ballotForkSourceExtract oa select n =
      ballotForkExtract (ballotForkComplete (select <$> oa)) n := by
  unfold ballotForkSourceExtract ballotForkExtract contextFork
  change Option.map Prod.snd <$> (Option.map _ <$> _) =
    Option.map (fun pair => ballotForkExtractPair pair.1 pair.2) <$>
      (Option.map PFunctor.FreeM.Cursor.SelectedForkView.outputs <$> _)
  simp only [Functor.map_map,Function.comp_def,Option.map_map]


section Probability
variable [Fintype F]
local instance sourceForkInhabited : Inhabited F := ⟨0⟩
noncomputable local instance sourceForkUniform : IsUniformSpec ((Unit →ₒ F) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

theorem ballotForkSourceExtract_probability_eq (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G) (n : Nat) :
    Pr[fun out => out.isSome | ballotForkSourceExtract oa select n] =
      Pr[fun out => out.isSome | ballotForkExtract (ballotForkComplete (select <$> oa)) n] := by
  rw [← ballotForkSourceExtract_project,probEvent_map]
  simp only [Function.comp_def,Option.isSome_map]

/-- The retained first output occurs in the original source, before completion. -/
theorem ballotForkSourceFirst_mem (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G)
    (path : PFunctor.FreeM.Path (ballotForkRunTrace (ballotForkComplete (select <$> oa)))) :
    ∃ cache, ((ballotForkSourceFirst oa select path).1,cache) ∈
      support (runBallotOracle oa ∅) := by
  have hs : ballotForkSourceFirst oa select path ∈ support (ballotForkSourceRun oa select) := by
    unfold ballotForkSourceFirst
    have supportedOutput {ι : Type} {spec : OracleSpec.{0,0} ι} {α : Type}
        (m : OracleComp spec α) (p : PFunctor.FreeM.Path m) :
        PFunctor.FreeM.output m p ∈ support m := by
      have hp : PFunctor.FreeM.output m p ∈ support
          (PFunctor.FreeM.output m <$> replayFirstPath m) := by
        rw [support_map]
        exact Set.mem_image_of_mem _ (mem_support_replayFirstPath m p)
      rwa [map_output_replayFirstPath] at hp
    exact supportedOutput _ _
  have hent := (mem_support_iff_of_evalSPMF_eq (ballotFork_entropy_eval
    (ballotForkSourceRun oa select)) _).mpr hs
  have hproject : ((ballotForkSourceFirst oa select path).1,
      ballotForkCacheProject (ballotForkSourceFirst oa select path).2.1) ∈ support
      (Prod.map id (fun state => ballotForkCacheProject state.1) <$>
        simulateQ ballotForkEntropyImpl (ballotForkSourceRun oa select)) := by
    rw [support_map]
    exact Set.mem_image_of_mem _ hent
  unfold ballotForkSourceRun at hproject
  rw [ballotFork_runtime_eq] at hproject
  simp only [ballotForkSourceComplete,runBallotOracle_bind,support_bind,Set.mem_iUnion] at hproject
  obtain ⟨out,hout,answer,_,hret⟩ := hproject
  have he : (ballotForkSourceFirst oa select path).1 = out.1 := by
    simpa [runBallotOracle] using congrArg Prod.fst (eq_of_mem_support_pure _ hret)
  exact ⟨out.2,he ▸ hout⟩

/-- Every returned source value is tied to this fork's first execution and
its selected statement; the extracted witness satisfies the actual relation. -/
theorem ballotForkSourceExtract_valid (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G) (n : Nat)
    (a : A) (stmt : BallotStatement G) (wit : BallotWitness F)
    (ho : some (a,stmt,wit) ∈ support (ballotForkSourceExtract oa select n)) :
    stmt.Witnesses wit ∧ stmt = (select a).1 ∧
      (∃ cache, (a,cache) ∈ support (runBallotOracle oa ∅)) ∧
      ∃ c : F, (select a).2.Valid (fun _ => c)
        stmt.generator stmt.publicKey stmt.ciphertext := by
  have hp : some (stmt,wit) ∈ support
      (Option.map Prod.snd <$> ballotForkSourceExtract oa select n) := by
    rw [support_map]
    exact ⟨some (a,stmt,wit),ho,rfl⟩
  rw [ballotForkSourceExtract_project] at hp
  have hv := ballotFork_extract_valid _ n stmt wit hp
  rw [ballotForkSourceExtract,support_map] at ho
  obtain ⟨result,hr,he⟩ := ho
  cases result with
  | none => simp at he
  | some w =>
    have he' := Option.some.inj he
    have ha : (ballotForkSourceFirst oa select w.view.firstPath).1 = a := congrArg Prod.fst he'
    have hstmt := congrArg (fun z => z.2.1) he'
    have ht := congrArg (fun t : BallotForkTrace F G => t.forgery.2.1.1)
      (ballotForkSourceFirst_trace oa select w.view.firstPath)
    change (select (ballotForkSourceFirst oa select w.view.firstPath).1).1 =
      w.outputs.1.forgery.2.1.1 at ht
    change w.outputs.1.forgery.2.1.1 = stmt at hstmt
    obtain ⟨cache,hcache⟩ := ballotForkSourceFirst_mem oa select w.view.firstPath
    have hw := contextForkWitness_success _ _ _ _ hr
    have hpath := replayPathResult_mem_support_replayFirstRun
      (ballotForkRunTrace (ballotForkComplete (select <$> oa))) w.view.firstPath
      (mem_support_replayFirstPath _ _)
    obtain ⟨c,_,_,hvalid⟩ := ballotFork_selected_challenge _ n w.outputs.1
      (PFunctor.FreeM.Path.trace _ w.view.firstPath) hpath w.label hw.2.2.1
    have hproof := congrArg (fun t : BallotForkTrace F G => t.forgery.2.2)
      (ballotForkSourceFirst_trace oa select w.view.firstPath)
    change (select (ballotForkSourceFirst oa select w.view.firstPath).1).2 =
      w.outputs.1.forgery.2.2 at hproof
    rw [ha] at hproof
    rw [← hproof,hstmt] at hvalid
    exact ⟨hv, hstmt.symm.trans (ht.symm.trans (congrArg (fun x => (select x).1) ha)),
      ⟨cache,ha ▸ hcache⟩,c,hvalid⟩

end Probability

#print axioms ballotForkRawSource_trace_eq
#print axioms ballotForkSourceExtract_probability_eq
#print axioms ballotForkSourceFirst_mem
#print axioms ballotForkSourceExtract_valid
#print axioms ballotForkSourceComplete_project
#print axioms ballotForkSource_trace_eq
#print axioms ballotForkSourceFirst_trace
#print axioms ballotForkSourceExtract_project
end ExplainableCrypto.Helios.Computational
