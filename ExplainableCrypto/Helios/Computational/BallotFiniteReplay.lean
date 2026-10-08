import ExplainableCrypto.Helios.Computational.BallotFiniteLogged
import ExplainableCrypto.Helios.Computational.BallotJointReplayTape

/-! The first execution and every conditional replay use the finite logging
interpreter. Saved input remains the existing finite tagged answer tape. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
open PFunctor.FreeM
variable {F G A : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F]
attribute [local implicit_reducible] ballotForkBudget

def ballotFiniteReplayTrace (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G) :
    OracleComp (FiatShamir.Fork.wrappedSpec F) (BallotForkTrace F G) :=
  ballotForkSourceTrace select <$> ballotFiniteReplaySourceRun oa

theorem ballotFiniteReplayTrace_eq (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G) :
    ballotFiniteReplayTrace oa select = ballotForkRunTrace (select <$> oa) := by
  unfold ballotFiniteReplayTrace
  rw [ballotFiniteReplaySourceRun_eq,ballotForkRawSource_trace_eq]

/-- The existing physical fork operation, decoded against the supplied lowered
query tree. This lets the finite interpreter supply every residual continuation. -/
def ballotLoggedReplayAtTape
    (main : OracleComp (FiatShamir.Fork.wrappedSpec F) (BallotForkTrace F G)) (n : Nat)
    (tape : PFunctor.TraceList (FiatShamir.Fork.wrappedSpec F).toPFunctor) :
    OracleComp (FiatShamir.Fork.wrappedSpec F)
      (Option (ContextForkWitness main (ballotForkBudget (F := F) n) (.inr ()))) :=
  match ballotReplayReadTape main tape with
  | none => pure none
  | some path =>
    match ballotForkSelector n (PFunctor.FreeM.output _ path) with
    | none => pure none
    | some s =>
      match PFunctor.FreeM.Cursor.locateAt? (P := (FiatShamir.Fork.wrappedSpec F).toPFunctor)
        (.inr ()) main path s with
      | none => pure none
      | some located =>
        (fun second => acceptContextForkWitness main (ballotForkBudget (F := F) n)
          (.inr ()) (ballotForkSelector n) s
          { occurrence := located.occurrence, first := located.completion, second := second }) <$>
          Cursor.completeOccurrence located.occurrence

def ballotFiniteSourceAttempt (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G) (n : Nat)
    (tape : PFunctor.TraceList (FiatShamir.Fork.wrappedSpec F).toPFunctor) :
    OracleComp (FiatShamir.Fork.wrappedSpec F) (Option (BallotWitness F)) :=
  Option.map (fun w => (ballotForkExtractPair w.outputs.1 w.outputs.2).2) <$>
    ballotLoggedReplayAtTape (ballotFiniteReplayTrace oa select) n tape

/-- On each actual shared original tape, the finite residual replay is exactly
the existing selected attempt, with its first proof and physical occurrence. -/
theorem ballotFiniteSourceAttempt_trace (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G) (n : Nat)
    (path : Path (ballotReplaySourceRun oa)) :
    ballotFiniteSourceAttempt oa select n (Path.trace _ path) =
      ballotReplaySourceAttempt oa select n path := by
  unfold ballotFiniteSourceAttempt
  rw [ballotFiniteReplayTrace_eq]
  unfold ballotLoggedReplayAtTape
  rw [← ballotReplaySourcePath_queries oa select path,ballotReplayReadTape_trace]
  unfold ballotReplaySourceAttempt ballotReplayAtPath
  dsimp only
  congr 1
  rcases hs : ballotForkSelector n (PFunctor.FreeM.output _ (ballotReplaySourcePath oa select path)) with _ | s
  · simp only
  · simp only
    rcases hl : PFunctor.FreeM.Cursor.locateAt?
      (P := (FiatShamir.Fork.wrappedSpec F).toPFunctor) (.inr ())
      (ballotForkRunTrace (select <$> oa)) (ballotReplaySourcePath oa select path) s with _ | located
    · simp only
    · simp only

private def withDecodedReplay (main : OracleComp (FiatShamir.Fork.wrappedSpec F)
    (A × FiatShamir.Fork.SimState Unit (BallotForkPoint G) F))
    (tape : PFunctor.TraceList (FiatShamir.Fork.wrappedSpec F).toPFunctor)
    (k : A → OracleComp (FiatShamir.Fork.wrappedSpec F)
      (Option (A × (Option (Fin 2) → BallotWitness F)))) :
    OracleComp (FiatShamir.Fork.wrappedSpec F) (Option (A × (Option (Fin 2) → BallotWitness F))) :=
  match ballotReplayReadTape main tape with
  | none => pure none
  | some path => k (PFunctor.FreeM.output _ path).1

def ballotFiniteJointReplayAtTape (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n : Nat)
    (tape : PFunctor.TraceList (FiatShamir.Fork.wrappedSpec F).toPFunctor) :
    OracleComp (FiatShamir.Fork.wrappedSpec F) (Option (A × (Option (Fin 2) → BallotWitness F))) :=
  withDecodedReplay (ballotFiniteReplaySourceRun oa) tape fun original => do
    let w0 ← ballotFiniteSourceAttempt oa (select (some 0)) n tape
    let w1 ← ballotFiniteSourceAttempt oa (select (some 1)) n tape
    let wa ← ballotFiniteSourceAttempt oa (select none) n tape
    pure (do return (original,ballotJointWitnesses (← w0) (← w1) (← wa)))

/-- One finite original execution, followed by three finite residual attempts. -/
def ballotFiniteJointReplay (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n : Nat) :
    OracleComp (FiatShamir.Fork.wrappedSpec F) (Option (A × (Option (Fin 2) → BallotWitness F))) := do
  let tape ← (ballotReplayCollectTape (ballotFiniteReplaySourceRun oa) :
    OracleComp (FiatShamir.Fork.wrappedSpec F) _)
  ballotFiniteJointReplayAtTape oa select n tape

theorem ballotFiniteJointReplayAtTape_trace (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n : Nat)
    (path : Path (ballotReplaySourceRun oa)) :
    ballotFiniteJointReplayAtTape oa select n (Path.trace _ path) =
      Option.map (fun w => ((PFunctor.FreeM.output _ path).1,w)) <$>
        ballotJointReplayAtPath oa select n path := by
  unfold ballotFiniteJointReplayAtTape
  rw [ballotFiniteReplaySourceRun_eq]
  unfold withDecodedReplay
  rw [ballotReplayReadTape_trace]
  rw [ballotFiniteSourceAttempt_trace,ballotFiniteSourceAttempt_trace,ballotFiniteSourceAttempt_trace]
  simp only [ballotJointReplayAtPath,map_bind]
  apply bind_congr
  intro w0
  apply bind_congr
  intro w1
  apply bind_congr
  intro wa
  cases w0 <;> cases w1 <;> cases wa <;> rfl

/-- Exact complete-algorithm equality. All four query trees now come from the
finite logging interpreter; no caller supplies state or replay correspondence. -/
theorem ballotFiniteJointReplay_eq (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n : Nat) :
    ballotFiniteJointReplay oa select n = ballotJointReplay oa select n := by
  have he : (ballotReplayCollectTape (ballotFiniteReplaySourceRun oa) :
      OracleComp (FiatShamir.Fork.wrappedSpec F) _) =
      Path.trace _ <$> replayFirstPath (ballotReplaySourceRun oa) := by
    rw [ballotFiniteReplaySourceRun_eq]
    exact ballotReplayCollectTape_eq _
  unfold ballotFiniteJointReplay ballotJointReplay
  rw [he,bind_map_left]
  exact bind_congr (fun path => ballotFiniteJointReplayAtTape_trace oa select n path)

#print axioms ballotFiniteReplayTrace_eq
#print axioms ballotFiniteSourceAttempt_trace
#print axioms ballotFiniteJointReplayAtTape_trace
#print axioms ballotFiniteJointReplay_eq
end ExplainableCrypto.Helios.Computational
