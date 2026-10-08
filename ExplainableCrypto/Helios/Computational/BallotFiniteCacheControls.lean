import ExplainableCrypto.Helios.Computational.BallotFiniteCache

/-! Finite cache controls distinguish complete statements and preserve answers
and prior entries. Concrete keys and answers are independent of proof machinery. -/
namespace ExplainableCrypto.Helios.Computational.BallotFiniteCacheControls
open OracleComp OracleSpec

def key0 : BallotStatement Nat × BallotCommitment Nat :=
  (⟨1,2,(3,4)⟩,((5,6),(7,8)))
def key1 : BallotStatement Nat × BallotCommitment Nat :=
  (⟨9,2,(3,4)⟩,((5,6),(7,8)))
def saved : BallotFiniteCache Bool Nat := (∅ : BallotFiniteCache Bool Nat).insert key0 false

def ask (key : BallotStatement Nat × BallotCommitment Nat) : BallotOracleComp Bool Nat Bool :=
  liftM ((BallotOracleSpec Bool Nat).query (.inr key))

/-- Cache hits preserve the existing answer and finite state and draw nothing. -/
theorem hit_preserves_runtime : runBallotFiniteCache (ask key0) saved = pure (false,saved) := by
  have h : saved.lookup key0 = some false := by decide
  simp [runBallotFiniteCache,ask,ballotFiniteCacheImpl,QueryImpl.add,StateT.run,h]

/-- A fresh full key samples once and retains the new answer in finite state. -/
theorem miss_samples_and_stores : runBallotFiniteCache (ask key1) saved =
    (do let answer ← uniformSample Bool; pure (answer,saved.insert key1 answer)) := by
  have h : saved.lookup key1 = none := by decide
  simp [runBallotFiniteCache,ask,ballotFiniteCacheImpl,QueryImpl.add,StateT.run,h]

/-- Equal commitments do not merge different full statements. -/
theorem full_key_separation : key0.2 = key1.2 ∧ key0 ≠ key1 ∧
    saved.lookup key0 = some false ∧ saved.lookup key1 = none := by decide

/-- Inserting a fresh second key keeps the first answer. Dropping prior state
or overwriting a hit with true gives an observably different cache. -/
theorem prior_answers_retained :
    (saved.insert key1 true).lookup key0 = some false ∧
    (saved.insert key1 true).lookup key1 = some true ∧
    BallotFiniteCache.denote (saved.insert key1 true) ≠
      BallotFiniteCache.denote ((∅ : BallotFiniteCache Bool Nat).insert key1 true) ∧
    saved.denote ≠ saved.denote.cacheQuery key0 true := by
  refine ⟨by decide,by decide,?_,?_⟩
  · intro h
    have hc : (some false : Option Bool) = none := congrFun h key0
    cases hc
  · intro h
    have hc := congrFun h key0
    have : (some false : Option Bool) = some true := hc
    cases this

/-- Two repeated requests remain one stored entry, by actual interpreter execution. -/
theorem repeated_query_one_entry :
    runBallotFiniteCache (do let _ ← ask key0; ask key0) saved = pure (false,saved) := by
  simp only [runBallotFiniteCache,simulateQ_bind,StateT.run_bind]
  change (runBallotFiniteCache (ask key0) saved >>= fun out =>
    runBallotFiniteCache (ask key0) out.2) = _
  rw [hit_preserves_runtime,pure_bind,hit_preserves_runtime]

#print axioms miss_samples_and_stores
#print axioms hit_preserves_runtime
#print axioms full_key_separation
#print axioms prior_answers_retained
#print axioms repeated_query_one_entry
end ExplainableCrypto.Helios.Computational.BallotFiniteCacheControls
