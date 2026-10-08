import ExplainableCrypto.Helios.Computational.BallotFiniteLogged
import ExplainableCrypto.Helios.Computational.BallotFiniteCacheControls

/-! Literal cache/log controls independent of cryptographic proof generation. -/
namespace ExplainableCrypto.Helios.Computational.BallotFiniteLoggedControls
open OracleComp OracleSpec BallotFiniteCacheControls

def after0 : BallotFiniteLoggedState Bool Nat := (saved,[((),key0)])

/-- A hit returns its old answer without entropy or a duplicate log entry. -/
theorem hit_no_draw_no_log : runBallotFiniteLogged (ask key0) after0 = pure (false,after0) := by
  have h : after0.1.lookup key0 = some false := by decide
  simp [runBallotFiniteLogged,ask,ballotFiniteLoggedImpl,QueryImpl.add,StateT.run,h]

/-- A miss draws exactly one wrapped challenge and appends the full key. -/
theorem miss_appends : runBallotFiniteLogged (ask key1) after0 =
    (do let c ← FiatShamir.Fork.wrappedChallengeQuery Bool
        pure (c,(saved.insert key1 c,[((),key0),((),key1)]))) := by
  have h : after0.1.lookup key1 = none := by decide
  simp [runBallotFiniteLogged,ask,ballotFiniteLoggedImpl,QueryImpl.add,StateT.run,h]
  rfl

/-- Forwarded uniform queries leave the cache and chronological miss log untouched. -/
theorem uniform_preserves_state :
    ((ballotFiniteLoggedImpl (F := Bool) (G := Nat)) (.inl 1)).run after0 =
      (do let u ← FiatShamir.Fork.wrappedUniformQuery Bool 1; pure (u,after0)) := rfl

/-- Two repeated hits keep one logged key and sample nothing. -/
theorem repeated_hit_no_duplicate :
    runBallotFiniteLogged (do let _ ← ask key0; ask key0) after0 = pure (false,after0) := by
  simp only [runBallotFiniteLogged,simulateQ_bind,StateT.run_bind]
  change (runBallotFiniteLogged (ask key0) after0 >>= fun out =>
    runBallotFiniteLogged (ask key0) out.2) = _
  rw [hit_no_draw_no_log,pure_bind,hit_no_draw_no_log]

/-- Log order and multiplicity distinguish the two tempting logging mutations;
equal commitments still have distinct full statement keys. -/
theorem detects_log_mutations :
    ([((),key0),((),key1)] : List (Unit × BallotForkPoint Nat)) ≠ [((),key1),((),key0)] ∧
    ([((),key0)] : List (Unit × BallotForkPoint Nat)) ≠ [((),key0),((),key0)] ∧
    key0.2 = key1.2 ∧ key0 ≠ key1 := by
  refine ⟨?_,?_,full_key_separation.1,full_key_separation.2.1⟩
  · intro h
    exact full_key_separation.2.1 (congrArg Prod.snd (List.cons.inj h).1)
  · intro h
    have he : (1 : Nat) = 2 := congrArg List.length h
    cases he

#print axioms hit_no_draw_no_log
#print axioms miss_appends
#print axioms uniform_preserves_state
#print axioms repeated_hit_no_duplicate
#print axioms detects_log_mutations
end ExplainableCrypto.Helios.Computational.BallotFiniteLoggedControls
