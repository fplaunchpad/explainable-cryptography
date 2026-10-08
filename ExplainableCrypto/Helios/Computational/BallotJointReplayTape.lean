import ExplainableCrypto.Helios.Computational.BallotReplayTape

/-! Shared-original joint replay from a finite tagged tape. Reconstruction
against the source derives the exact physical paths used by the existing fork. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
open PFunctor.FreeM
variable {F G A : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F]

def ballotJointReplayAtTape (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n : Nat)
    (tape : PFunctor.TraceList (FiatShamir.Fork.wrappedSpec F).toPFunctor) :
    OracleComp (FiatShamir.Fork.wrappedSpec F) (Option (A × (Option (Fin 2) → BallotWitness F))) :=
  match ballotReplayReadTape (ballotReplaySourceRun oa) tape with
  | none => pure none
  | some path => Option.map (fun w => ((PFunctor.FreeM.output _ path).1,w)) <$>
      ballotJointReplayAtPath oa select n path

/-- No tape, cache or path-validity premise is supplied by the caller. -/
def ballotJointReplayTape (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n : Nat) :
    OracleComp (FiatShamir.Fork.wrappedSpec F) (Option (A × (Option (Fin 2) → BallotWitness F))) := do
  let tape ← (ballotReplayCollectTape (ballotReplaySourceRun oa) :
    OracleComp (FiatShamir.Fork.wrappedSpec F) _)
  ballotJointReplayAtTape oa select n tape

/-- All three attempts reconstruct the very same original path, including all
uniform/hash answers and selected physical occurrences. -/
theorem ballotJointReplayAtTape_trace (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n : Nat)
    (path : Path (ballotReplaySourceRun oa)) :
    ballotJointReplayAtTape oa select n (Path.trace _ path) =
      Option.map (fun w => ((PFunctor.FreeM.output _ path).1,w)) <$>
        ballotJointReplayAtPath oa select n path := by
  unfold ballotJointReplayAtTape
  rw [ballotReplayReadTape_trace]

/-- Exact algorithm equality retains the original source result, all three
attempts, acceptance tests and randomness. No correspondence premise is assumed. -/
theorem ballotJointReplayTape_eq (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n : Nat) :
    ballotJointReplayTape oa select n = ballotJointReplay oa select n := by
  have he : (ballotReplayCollectTape (ballotReplaySourceRun oa) :
      OracleComp (FiatShamir.Fork.wrappedSpec F) _) =
      Path.trace _ <$> replayFirstPath (ballotReplaySourceRun oa) :=
    ballotReplayCollectTape_eq _
  unfold ballotJointReplayTape ballotJointReplay
  rw [he,bind_map_left]
  exact bind_congr (fun path => ballotJointReplayAtTape_trace oa select n path)

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [SampleableType F] in
/-- The saved entropy tape has at most m entries from raw source bound m. -/
theorem ballotJointReplayTape_saved_length_le (oa : BallotOracleComp F G A)
    (m : Nat) (hb : oa.IsTotalQueryBound m)
    (tape : PFunctor.TraceList (FiatShamir.Fork.wrappedSpec F).toPFunctor)
    (ht : tape ∈ support (ballotReplayCollectTape (ballotReplaySourceRun oa) :
      OracleComp (FiatShamir.Fork.wrappedSpec F) _)) : tape.length ≤ m :=
  ballotReplayCollectTape_length_le _ m (ballotReplaySourceRun_total_query_bound oa m hb) tape ht

#print axioms ballotJointReplayAtTape_trace
#print axioms ballotJointReplayTape_eq
#print axioms ballotJointReplayTape_saved_length_le
end ExplainableCrypto.Helios.Computational
