import ExplainableCrypto.Helios.Computational.BallotFiniteCache
import ExplainableCrypto.Helios.Computational.BallotReplaySource
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-! Finite live state for the existing replay logging interpreter. Hash misses
append their full key to the ordered log; hits and uniform queries leave it alone. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G A : Type} [DecidableEq G]

abbrev BallotFiniteLoggedState (F G : Type) :=
  BallotFiniteCache F G × List (Unit × BallotForkPoint G)

def BallotFiniteLoggedState.denote (s : BallotFiniteLoggedState F G) :
    FiatShamir.Fork.SimState Unit (BallotForkPoint G) F :=
  (fun key => s.1.lookup key.2,s.2)

@[simp]
theorem BallotFiniteLoggedState.denote_empty :
    (denote (∅,[]) : FiatShamir.Fork.SimState Unit (BallotForkPoint G) F) = (∅,[]) := rfl

private theorem denote_insert (s : BallotFiniteLoggedState F G)
    (key : BallotForkPoint G) (c : F) :
    BallotFiniteLoggedState.denote (s.1.insert key c,s.2 ++ [((),key)]) =
      (s.denote.1.cacheQuery ((),key) c,s.2 ++ [((),key)]) := by
  apply Prod.ext
  · funext other
    rcases other with ⟨⟨⟩,other⟩
    by_cases h : other = key
    · subst other; simp [BallotFiniteLoggedState.denote]
    · simp [BallotFiniteLoggedState.denote,h]
  · rfl

def ballotFiniteLoggedImpl : QueryImpl (BallotOracleSpec F G)
    (StateT (BallotFiniteLoggedState F G) (OracleComp (FiatShamir.Fork.wrappedSpec F))) :=
  QueryImpl.add (spec₁ := unifSpec) (spec₂ := BallotHashSpec F G)
    (fun n s => do
      let u ← FiatShamir.Fork.wrappedUniformQuery F n
      pure (u,s))
    (fun key s => match s.1.lookup key with
      | some c => pure (c,s)
      | none => do
        let c ← FiatShamir.Fork.wrappedChallengeQuery F
        pure (c,(s.1.insert key c,s.2 ++ [((),key)])))

def runBallotFiniteLogged (oa : BallotOracleComp F G A) (s : BallotFiniteLoggedState F G) :=
  (simulateQ ballotFiniteLoggedImpl oa).run s

private theorem finiteLogged_step_eq (t : (BallotOracleSpec F G).Domain)
    (s : BallotFiniteLoggedState F G) :
    Prod.map id BallotFiniteLoggedState.denote <$> (ballotFiniteLoggedImpl t).run s =
      (ballotForkLoggedImpl t).run s.denote := by
  cases t with
  | inl n =>
    change _ = (FiatShamir.Fork.unifForward Unit (BallotForkPoint G) F n).run s.denote
    rw [FiatShamir.Fork.unifForward_run]
    simp [ballotFiniteLoggedImpl,QueryImpl.add,StateT.run]
  | inr key =>
    change _ = (FiatShamir.Fork.roImpl Unit (BallotForkPoint G) F ((),key)).run s.denote
    cases h : s.1.lookup key with
    | some c =>
      rw [FiatShamir.Fork.roImpl_run_some (hcache := h)]
      simp [ballotFiniteLoggedImpl,QueryImpl.add,StateT.run,h]
    | none =>
      rw [FiatShamir.Fork.roImpl_run_none (hcache := h)]
      simp [ballotFiniteLoggedImpl,QueryImpl.add,StateT.run,h,denote_insert]
      rfl

/-- Exact full-program correspondence preserves output, final cache, ordered
miss log and entropy queries, without a caller-supplied state invariant. -/
theorem runBallotFiniteLogged_eq (oa : BallotOracleComp F G A) (s : BallotFiniteLoggedState F G) :
    Prod.map id BallotFiniteLoggedState.denote <$> runBallotFiniteLogged oa s =
      (simulateQ ballotForkLoggedImpl oa).run s.denote := by
  exact map_run_simulateQ_eq_of_query_map_eq ballotFiniteLoggedImpl ballotForkLoggedImpl
    BallotFiniteLoggedState.denote finiteLogged_step_eq oa s

/-- Lower the source with finite internal cache state and project its final
state to the established replay interface. -/
def ballotFiniteReplaySourceRun (oa : BallotOracleComp F G A) :
    OracleComp (FiatShamir.Fork.wrappedSpec F)
      (A × FiatShamir.Fork.SimState Unit (BallotForkPoint G) F) :=
  Prod.map id BallotFiniteLoggedState.denote <$> runBallotFiniteLogged oa (∅,[])

theorem ballotFiniteReplaySourceRun_eq (oa : BallotOracleComp F G A) :
    ballotFiniteReplaySourceRun oa = ballotReplaySourceRun oa := by
  unfold ballotFiniteReplaySourceRun
  rw [runBallotFiniteLogged_eq,BallotFiniteLoggedState.denote_empty]

/-- The finite miss log inherits the existing source hash-query bound. Its
initial log is retained, with at most n additional entries. -/
theorem runBallotFiniteLogged_log_length_le [Field F] [SampleableType F] [Fintype F]
    (oa : BallotOracleComp F G A) (n : Nat)
    (hb : oa.IsQueryBoundP (isBallotHashQuery (F := F)) n)
    (s : BallotFiniteLoggedState F G) (out : A × BallotFiniteLoggedState F G)
    (ho : out ∈ support (runBallotFiniteLogged oa s)) : out.2.2.length ≤ s.2.length+n := by
  have hs : (out.1,out.2.denote) ∈ support ((simulateQ ballotForkLoggedImpl oa).run s.denote) := by
    rw [← runBallotFiniteLogged_eq,support_map]
    exact ⟨out,ho,rfl⟩
  exact ballotFork_log_bound oa n hb s.denote (out.1,out.2.denote) hs

#print axioms BallotFiniteLoggedState.denote_empty
#print axioms runBallotFiniteLogged_eq
#print axioms ballotFiniteReplaySourceRun_eq
#print axioms runBallotFiniteLogged_log_length_le
end ExplainableCrypto.Helios.Computational
