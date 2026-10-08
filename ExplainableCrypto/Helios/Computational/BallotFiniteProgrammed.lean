import ExplainableCrypto.Helios.Computational.BallotFiniteCache
import ExplainableCrypto.Helios.Computational.BallotProgrammedOracle

/-! Finite shadow state for the actual programmed proof interpreter. Projection
preserves its cache, sticky collision flag and exact request history. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec

structure BallotFiniteProgrammedState (F G : Type) where
  cache : BallotFiniteCache F G
  bad : Bool
  programmed : List (BallotStatement G)

variable {F G : Type} [DecidableEq G]

def BallotFiniteProgrammedState.empty : BallotFiniteProgrammedState F G := ⟨∅,false,[]⟩

def BallotFiniteProgrammedState.denote (s : BallotFiniteProgrammedState F G) :
    BallotProgrammedState F G := ⟨s.cache.denote,s.bad,s.programmed⟩

@[simp]
theorem BallotFiniteProgrammedState.denote_empty :
    (empty : BallotFiniteProgrammedState F G).denote = BallotProgrammedState.empty := rfl

variable [Field F] [AddCommGroup G] [Module F G]

/-- Apply an actually sampled transcript. Occupied keys are always flagged,
even when the old and sampled challenges agree; every request is recorded. -/
def BallotFiniteProgrammedState.program (s : BallotFiniteProgrammedState F G)
    (stmt : BallotStatement G) (t : BallotCommitment G × F × BallotResponse F) :
    Proof01 F G × BallotFiniteProgrammedState F G :=
  let p := ballotTranscriptProof t.1 t.2.1 t.2.2
  match s.cache.lookup (stmt,t.1) with
  | some _ => (p,⟨s.cache,true,stmt :: s.programmed⟩)
  | none => (p,⟨s.cache.insert (stmt,t.1) t.2.1,s.bad,stmt :: s.programmed⟩)

def ballotFiniteProgrammedRaw : QueryImpl (BallotOracleSpec F G)
    (StateT (BallotFiniteProgrammedState F G) (BallotOracleComp F G)) :=
  QueryImpl.add (spec₁ := unifSpec) (spec₂ := BallotHashSpec F G)
    (fun n s => do
      let u ← liftM ((BallotOracleSpec F G).query (.inl n))
      pure (u,s))
    (fun key s => match s.cache.lookup key with
      | some c => pure (c,s)
      | none => do
        let c ← ballotChallengeOracle key.1 key.2
        pure (c,{s with cache := s.cache.insert key c}))

variable [SampleableType F]

def ballotFiniteProgrammedImpl (g pk : G) : QueryImpl (BallotProofOracleSpec F G)
    (StateT (BallotFiniteProgrammedState F G) (BallotOracleComp F G)) :=
  QueryImpl.add (spec₁ := BallotOracleSpec F G) (spec₂ := HonestBallotProofSpec F G)
    ballotFiniteProgrammedRaw
    (fun wit s => do
      let stmt := honestProofStatement g pk wit
      let t ← liftComp (ballotFullSimTranscript (F := F) stmt) (BallotOracleSpec F G)
      pure (s.program stmt t))

omit [Field F] [AddCommGroup G] [Module F G] [SampleableType F] in
private theorem raw_step_eq (t : (BallotOracleSpec F G).Domain)
    (s : BallotFiniteProgrammedState F G) :
    Prod.map id BallotFiniteProgrammedState.denote <$>
      ((ballotFiniteProgrammedRaw t).run s) = (ballotProgrammedRaw t).run s.denote := by
  cases t with
  | inl n => simp [ballotFiniteProgrammedRaw,ballotProgrammedRaw,QueryImpl.add,StateT.run]
  | inr key =>
    simp only [ballotFiniteProgrammedRaw,ballotProgrammedRaw,QueryImpl.add,StateT.run,
      BallotFiniteProgrammedState.denote]
    rw [show s.cache.denote key = s.cache.lookup key from rfl]
    cases h : s.cache.lookup key <;>
      simp [BallotFiniteProgrammedState.denote,BallotFiniteCache.denote_insert]

private theorem programmed_step_eq (g pk : G) (t : (BallotProofOracleSpec F G).Domain)
    (s : BallotFiniteProgrammedState F G) :
    Prod.map id BallotFiniteProgrammedState.denote <$>
      ((ballotFiniteProgrammedImpl g pk t).run s) =
      (ballotProgrammedImpl g pk t).run s.denote := by
  cases t with
  | inl t => exact raw_step_eq t s
  | inr wit =>
    simp only [ballotFiniteProgrammedImpl,ballotProgrammedImpl,ballotProgrammedStatement,QueryImpl.add,StateT.run,
      strongBallotSimOracle,liftComp_bind,map_bind,bind_assoc]
    apply bind_congr
    intro transcript
    rw [show s.denote.cache (honestProofStatement g pk wit,transcript.1) =
      s.cache.lookup (honestProofStatement g pk wit,transcript.1) from rfl]
    cases h : s.cache.lookup (honestProofStatement g pk wit,transcript.1) <;>
      simp [BallotFiniteProgrammedState.program,h,BallotFiniteProgrammedState.denote,
        BallotFiniteCache.denote_insert]

/-- Exact correspondence for arbitrary proof-oracle programs and finite initial
states. No reachability, live/shadow invariant or caller presentation is assumed. -/
theorem runBallotFiniteProgrammed_eq {α : Type} (g pk : G)
    (oa : OracleComp (BallotProofOracleSpec F G) α) (s : BallotFiniteProgrammedState F G) :
    Prod.map id BallotFiniteProgrammedState.denote <$>
      (simulateQ (ballotFiniteProgrammedImpl g pk) oa).run s =
      (simulateQ (ballotProgrammedImpl g pk) oa).run s.denote := by
  exact map_run_simulateQ_eq_of_query_map_eq
    (ballotFiniteProgrammedImpl g pk) (ballotProgrammedImpl g pk)
    BallotFiniteProgrammedState.denote (programmed_step_eq g pk) oa s

/-- Both shadow and live caches are finite in this complete execution. -/
def runBallotFiniteProgrammed {α : Type} (g pk : G)
    (oa : OracleComp (BallotProofOracleSpec F G) α) :
    ProbComp ((α × BallotFiniteProgrammedState F G) × BallotFiniteCache F G) :=
  runBallotFiniteCache ((simulateQ (ballotFiniteProgrammedImpl g pk) oa).run .empty) ∅

/-- Composition retains the output, both final caches, collision flag and exact
request history, with the same explicit random computation. -/
theorem runBallotFiniteProgrammed_runtime {α : Type} (g pk : G)
    (oa : OracleComp (BallotProofOracleSpec F G) α) :
    (fun out => ((out.1.1,out.1.2.denote),out.2.denote)) <$>
      runBallotFiniteProgrammed g pk oa = runBallotProgrammed g pk oa := by
  have hl := runBallotFiniteCache_eq
    ((simulateQ (ballotFiniteProgrammedImpl g pk) oa).run .empty) ∅
  have hs := runBallotFiniteProgrammed_eq g pk oa .empty
  rw [BallotFiniteProgrammedState.denote_empty] at hs
  have h := congrArg (fun p => runBallotOracle p (∅ : BallotOracleCache F G)) hs
  simp only [runBallotOracle,simulateQ_map,StateT.run_map] at h
  unfold runBallotProgrammed runBallotOracle
  rw [← h]
  change _ = (fun out => ((out.1.1,out.1.2.denote),out.2)) <$>
    runBallotOracle ((simulateQ (ballotFiniteProgrammedImpl g pk) oa).run .empty) ∅
  simp only [BallotFiniteCache.denote_empty] at hl
  rw [← hl]
  simp [runBallotFiniteProgrammed,Functor.map_map]

#print axioms BallotFiniteProgrammedState.denote_empty
#print axioms runBallotFiniteProgrammed_eq
#print axioms runBallotFiniteProgrammed_runtime
end ExplainableCrypto.Helios.Computational
