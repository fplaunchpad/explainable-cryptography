import ExplainableCrypto.Helios.Computational.CacheHashDispatchSource

/-! Complete executed-request controls. Expected scalar digits, chronological
order and consumed entropy are derived independently of the dispatcher. -/
namespace ExplainableCrypto.Helios.Computational.CacheHashDispatchControls
open OracleComp OracleSpec BitOracleMachine CacheHashDispatch BallotCacheCodecControls
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
set_option maxRecDepth 8192

private def handler : QueryImpl spec (StateT (List Bool) Id) := fun r tape =>
  match r with
  | .coin => (tape.headD false,tape.tail)
  | .hash word => (word,tape)

def trace (c : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11))
    (log : List (Unit × BallotForkPoint (PrimeGroup 23 11))) (slack : Nat) (tape : List Bool) :
    Config 12 size 3 × List Bool :=
  (simulateQ handler (Prod.fst <$> run code (requestClock c key log slack)
    (start ((ballotKeyBitCodec 23 11).encode key) ((ballotCacheBitCodec 23 11).encode c)
      (((ballotLogEntryBitCodec 23 11).list).encode log) (SamplerOperands.input slack 11 [])))).run tape

private theorem trace_eq (c : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11))
    (log : List (Unit × BallotForkPoint (PrimeGroup 23 11))) (slack : Nat) (tape : List Bool) :
    trace c log slack tape = (simulateQ handler (request c key log slack)).run tape := by
  unfold trace
  rw [(request_run c key log slack).1]

/-- The stored value is three, whose independently derived prefix is 11011;
a cache hit leaves every supplied coin available and preserves the log. -/
theorem hit_control : trace cache [((),otherKey)] 2 [true,false,true] =
    (result ((ballotKeyBitCodec 23 11).encode key) ((ballotCacheBitCodec 23 11).encode cache)
      (((ballotLogEntryBitCodec 23 11).list).encode [((),otherKey)]) (SamplerOperands.input 2 11 [])
      [true,true,false,true,true],[true,false,true]) := by
  rw [trace_eq]
  have found : cache.lookup key = some 3 := by decide +kernel
  rw [request,found]
  rfl

/-- Chronological bits 0110 encode six. Exactly four coins are consumed; the
new cache stores six, and the new key follows the old log entry. -/
theorem miss_control : trace ∅ [((),otherKey)] 0 [false,true,true,false,true] =
    (result ((ballotKeyBitCodec 23 11).encode key)
      ((ballotCacheBitCodec 23 11).encode ((∅ : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11)).insert key 6))
      (((ballotLogEntryBitCodec 23 11).list).encode [((),otherKey),((),key)]) (SamplerOperands.input 0 11 [])
      [true,true,true,false,false,true,true],[true]) := by
  rw [trace_eq]
  rfl

/-- Zero remains a valid scalar; a miss executes and records it rather than
rejecting the one-bit canonical zero prefix. -/
theorem zero_control : trace ∅ [] 0 [false,false,false,false,true] =
    (result ((ballotKeyBitCodec 23 11).encode key)
      ((ballotCacheBitCodec 23 11).encode ((∅ : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11)).insert key 0))
      (((ballotLogEntryBitCodec 23 11).list).encode [((),key)]) (SamplerOperands.input 0 11 [])
      [false],[true]) := by
  rw [trace_eq]
  rfl

/-- An always-sampling hit implementation would consume this first true coin. -/
theorem hit_not_sampled : (trace cache [((),otherKey)] 2 [true,false,true]).2 ≠ [false,true] := by
  rw [hit_control]
  decide +kernel

/-- Six is distinguished from the tempting constant-zero sampler. -/
theorem miss_not_zero : (trace ∅ [((),otherKey)] 0 [false,true,true,false,true]).1.stk 7 ≠ [false] := by
  rw [miss_control]
  decide +kernel

/-- A prepend log mutation changes the actual request's returned log word. -/
theorem log_not_prepend : (trace ∅ [((),otherKey)] 0 [false,true,true,false,true]).1.stk 10 ≠
    (((ballotLogEntryBitCodec 23 11).list).encode [((),key),((),otherKey)]) := by
  rw [miss_control]
  decide +kernel

/-- Every work port is empty after the complete miss; key and operand record
remain present rather than being silently lost by a cleanup. -/
theorem miss_frame_control :
    let out := (trace ∅ [((),otherKey)] 0 [false,true,true,false,true]).1
    (∀ k : Fin 7, out.stk ⟨k.val,by omega⟩ = []) ∧
      out.stk 8 = (ballotKeyBitCodec 23 11).encode key ∧
      out.stk 11 = SamplerOperands.input 0 11 [] := by
  rw [miss_control]
  refine ⟨?_,rfl,rfl⟩
  intro k
  fin_cases k <;> rfl

end ExplainableCrypto.Helios.Computational.CacheHashDispatchControls
