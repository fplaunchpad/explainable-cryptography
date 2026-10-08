import ExplainableCrypto.Helios.Computational.CacheRequestPrefixes
import ExplainableCrypto.Helios.Computational.CacheHashCoins

/-! Kernel controls for original request observations. Expected answers, cache
insertion order, chronological log and prestates are written independently of
the observer. These are finite interpreter controls, not protocol secrecy. -/
namespace ExplainableCrypto.Helios.Computational.CacheRequestPrefixControls
open OracleComp OracleSpec BallotCacheCodecControls
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
set_option maxRecDepth 16384

private abbrev F := ZMod 11
private abbrev G := PrimeGroup 23 11

def initial : BallotFiniteLoggedState F G :=
  ((∅ : BallotFiniteCache F G).insert key 3,[((),otherKey),((),key)])

def finalState : BallotFiniteLoggedState F G :=
  (initial.1.insert otherKey 6,[((),otherKey),((),key),((),otherKey)])

/-- Three old/new cache hits surround an intervening uniform and one fresh miss. -/
def source : BallotOracleComp F G (List Nat) := do
  let a : F ← liftM ((BallotOracleSpec F G).query (.inr key))
  let u : Fin 4 ← liftM ((BallotOracleSpec F G).query (.inl 3))
  let b : F ← liftM ((BallotOracleSpec F G).query (.inr key))
  let c : F ← liftM ((BallotOracleSpec F G).query (.inr otherKey))
  let d : F ← liftM ((BallotOracleSpec F G).query (.inr otherKey))
  pure [a.val,u.val,b.val,c.val,d.val]

private def handler : QueryImpl unifSpec (StateT (List Nat) Id) := fun n tape =>
  (⟨tape.headD 0 % (n+1),Nat.mod_lt _ (by omega)⟩,tape.tail)

def trace : (List Nat × CacheRequestPrefixes.State F G) × List Nat :=
  (simulateQ handler (simulateQ CacheHashCoins.exactChallenge
    (CacheRequestPrefixes.run source initial))).run [2,6,9]

def expectedEvents : List (CacheRequestPrefixes.Event F G) :=
  [(.inr key,initial),(.inl 3,initial),(.inr key,initial),
   (.inr otherKey,initial),(.inr otherKey,finalState)]

/-- Uniform answer two and fresh challenge six consume exactly two supplied
answers. All five original invocations remain, including all three hits. The
fresh miss records the old state, and the following hit records its successor. -/
theorem complete_trace_control :
    trace = (([3,2,3,6,6],(finalState,expectedEvents)),[9]) := by
  rfl

/-- The nonempty offsets really contain one cache entry and two log entries;
the fresh insertion increments each once despite repeated requests. -/
theorem offset_control :
    initial.1.entries.length = 1 ∧ initial.2.length = 2 ∧
    trace.1.2.1.1.entries.length = 2 ∧ trace.1.2.1.2.length = 3 := by
  rw [complete_trace_control]
  decide +kernel

/-- Omitting deterministic cache hits would leave only the uniform and miss. -/
theorem hits_not_omitted : trace.1.2.2 ≠
    [(.inl 3,initial),(.inr otherKey,initial)] := by
  rw [complete_trace_control]
  intro h
  have := congrArg List.length h
  change 5 = 2 at this
  omega

/-- Uniforms are original requests even though they do not grow cache or log. -/
theorem uniform_not_omitted : trace.1.2.2 ≠
    [(.inr key,initial),(.inr key,initial),
     (.inr otherKey,initial),(.inr otherKey,finalState)] := by
  rw [complete_trace_control]
  intro h
  have := congrArg List.length h
  change 5 = 4 at this
  omega

/-- The fourth event is the fresh miss's input state, not its poststate. -/
theorem miss_not_poststate : trace.1.2.2[3]?.map (fun e => e.2.1.entries.length) ≠
    some finalState.1.entries.length := by
  rw [complete_trace_control]
  decide +kernel

#print axioms complete_trace_control
#print axioms offset_control
#print axioms hits_not_omitted
#print axioms uniform_not_omitted
#print axioms miss_not_poststate
end ExplainableCrypto.Helios.Computational.CacheRequestPrefixControls
