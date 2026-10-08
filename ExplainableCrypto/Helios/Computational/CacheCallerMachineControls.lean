import ExplainableCrypto.Helios.Computational.CacheCallerMachineRun

/-! Kernel controls for resident caller entry and return. Saved words are private
machine data; retaining them here does not add protocol observations. -/
namespace ExplainableCrypto.Helios.Computational.CacheCallerMachineControls
open OracleComp OracleSpec BitOracleMachine CacheCallerMachine BallotCacheCodecControls
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
set_option maxRecDepth 8192

private def handler : QueryImpl spec (StateT (List Bool) Id) := fun r tape =>
  match r with
  | .coin => (tape.headD false,tape.tail)
  | .hash word => (word,tape)

/-- Observe the executed resident caller with its old answer and saved word. -/
def trace (c : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11))
    (log : List (Unit × BallotForkPoint (PrimeGroup 23 11))) (slack : Nat)
    (previous saved tape : List Bool) : Config 13 size 3 × List Bool :=
  (simulateQ handler (Prod.fst <$> run code (clock c key log slack previous)
    (start ((ballotKeyBitCodec 23 11).encode key) ((ballotCacheBitCodec 23 11).encode c)
      (((ballotLogEntryBitCodec 23 11).list).encode log)
      (SamplerOperands.input slack 11 []) previous saved))).run tape

private theorem trace_eq (c : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11))
    (log : List (Unit × BallotForkPoint (PrimeGroup 23 11))) (slack : Nat)
    (previous saved tape : List Bool) :
    trace c log slack previous saved tape =
      (simulateQ handler ((fun cfg => result cfg saved) <$>
        CacheHashDispatch.request c key log slack)).run tape := by
  unfold trace
  rw [(request_run c key log slack previous saved).1]

private theorem result_ports (key cache log record answer saved : List Bool) :
    result (CacheHashDispatch.result key cache log record answer) saved =
      (⟨none,2,![[],[],[],[],[],[],[],answer,key,cache,log,record,saved]⟩ : Config 13 size 3) := by
  change (⟨none,2,_⟩ : Config 13 size 3) = _
  congr 1
  funext k
  fin_cases k <;> rfl

private def oldAnswer : List Bool := [true,false,true]
private def savedWord : List Bool := [false,false,true,false,true]

/-- Nonempty resident cache/log and saved data survive a cache hit. Stored
three has independently derived prefix 11011; no supplied coin is consumed. -/
theorem hit_control : trace cache [((),otherKey)] 2 oldAnswer savedWord [true,false,true] =
    ((⟨none,2,![[],[],[],[],[],[],[],[true,true,false,true,true],
      (ballotKeyBitCodec 23 11).encode key,(ballotCacheBitCodec 23 11).encode cache,
      (((ballotLogEntryBitCodec 23 11).list).encode [((),otherKey)]),
      (SamplerOperands.input 2 11 []),savedWord]⟩ : Config 13 size 3),[true,false,true]) := by
  rw [trace_eq]
  have found : cache.lookup key = some 3 := by decide +kernel
  rw [CacheHashDispatch.request,found]
  change (result _ savedWord,[true,false,true]) = _
  rw [result_ports]
  rfl

def missCache : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11) :=
  (∅ : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11)).insert otherKey 5

/-- Coins 0110 give six. A fresh miss retains the existing other-key entry,
appends the requested key to the log, clears the previous answer and preserves
the entire saved word; the final true coin remains unused. -/
theorem miss_control :
    trace missCache [((),otherKey)] 0 oldAnswer savedWord [false,true,true,false,true] =
    ((⟨none,2,![[],[],[],[],[],[],[],[true,true,true,false,false,true,true],
      (ballotKeyBitCodec 23 11).encode key,
      (ballotCacheBitCodec 23 11).encode (missCache.insert key 6),
      (((ballotLogEntryBitCodec 23 11).list).encode [((),otherKey),((),key)]),
      (SamplerOperands.input 0 11 []),savedWord]⟩ : Config 13 size 3),[true]) := by
  rw [trace_eq]
  change (result (CacheHashDispatch.result _ _ _ _ _) savedWord,[true]) = _
  rw [result_ports]
  rfl

/-- Old response bits cannot contaminate the new scalar word. -/
theorem old_answer_not_appended :
    (trace missCache [((),otherKey)] 0 oldAnswer savedWord [false,true,true,false,true]).1.stk 7 ≠
      [true,true,true,false,false,true,true]++oldAnswer := by
  rw [miss_control]
  decide +kernel

/-- Saved data is nonempty and survives the complete miss, not merely its gate. -/
theorem saved_frame_control :
    (trace missCache [((),otherKey)] 0 oldAnswer savedWord [false,true,true,false,true]).1.stk 12 =
      [false,false,true,false,true] ∧ savedWord ≠ [] := by
  rw [miss_control]
  decide +kernel

/-- Reenter the actual first returned configuration, changing only finite
control. The new cache/log, old response and saved word stay resident. -/
def repeatedTrace : Config 13 size 3 × List Bool :=
  let first := trace missCache [((),otherKey)] 0 oldAnswer savedWord [false,true,true,false,true]
  (simulateQ handler (Prod.fst <$> run code
    (clock (missCache.insert key 6) key [((),otherKey),((),key)] 0 (first.1.stk 7))
    {first.1 with l := some 0, var := 0})).run first.2

/-- The next resident entry is a hit on the just-inserted six. It consumes no
further coins, makes no duplicate log entry, and returns the same full layout. -/
theorem repeated_entry_control : repeatedTrace =
    ((⟨none,2,![[],[],[],[],[],[],[],[true,true,true,false,false,true,true],
      (ballotKeyBitCodec 23 11).encode key,
      (ballotCacheBitCodec 23 11).encode (missCache.insert key 6),
      (((ballotLogEntryBitCodec 23 11).list).encode [((),otherKey),((),key)]),
      (SamplerOperands.input 0 11 []),savedWord]⟩ : Config 13 size 3),[true]) := by
  unfold repeatedTrace
  rw [miss_control]
  have restart :
      (⟨some 0,0,![[],[],[],[],[],[],[],[true,true,true,false,false,true,true],
        (ballotKeyBitCodec 23 11).encode key,
        (ballotCacheBitCodec 23 11).encode (missCache.insert key 6),
        (((ballotLogEntryBitCodec 23 11).list).encode [((),otherKey),((),key)]),
        (SamplerOperands.input 0 11 []),savedWord]⟩ : Config 13 size 3) =
      start ((ballotKeyBitCodec 23 11).encode key)
        ((ballotCacheBitCodec 23 11).encode (missCache.insert key 6))
        (((ballotLogEntryBitCodec 23 11).list).encode [((),otherKey),((),key)])
        (SamplerOperands.input 0 11 []) [true,true,true,false,false,true,true] savedWord := by
    change (⟨some 0,0,_⟩ : Config 13 size 3) = ⟨some 0,0,_⟩
    congr 1
    funext k
    fin_cases k <;> rfl
  dsimp only
  rw [restart]
  change trace (missCache.insert key 6) [((),otherKey),((),key)] 0
    [true,true,true,false,false,true,true] savedWord [true] = _
  rw [trace_eq]
  have found : (missCache.insert key 6).lookup key = some 6 := by decide +kernel
  rw [CacheHashDispatch.request,found]
  change (result (CacheHashDispatch.result _ _ _ _ _) savedWord,[true]) = _
  rw [result_ports]
  rfl

/-- Failed request return preserves every caller port, including saved data,
and rejects in exactly one transition of charge three. -/
theorem failed_return_control (words : Fin 13 → List Bool) :
    step code (⟨some returnLabel,0,words⟩ : Config 13 size 3) =
      pure ((⟨none,0,words⟩ : Config 13 size 3),3) := by
  rfl

/-- The other nonsuccess memory value also rejects rather than being treated
as a Boolean success flag. -/
theorem nonzero_failure_control (words : Fin 13 → List Bool) :
    step code (⟨some returnLabel,1,words⟩ : Config 13 size 3) =
      pure ((⟨none,0,words⟩ : Config 13 size 3),3) := by
  rfl

/-- Only the actual success value two passes the return guard. -/
theorem successful_return_control (words : Fin 13 → List Bool) :
    step code (⟨some returnLabel,2,words⟩ : Config 13 size 3) =
      pure ((⟨none,2,words⟩ : Config 13 size 3),3) := by
  rfl

/-- A failed return cannot be replaced by an unconditional successful halt. -/
theorem failed_return_not_success (words : Fin 13 → List Bool) :
    (fun out => out.1.var.val) <$>
      step code (⟨some returnLabel,0,words⟩ : Config 13 size 3) ≠ pure 2 := by
  rw [failed_return_control]
  simp

#print axioms failed_return_control
#print axioms nonzero_failure_control
#print axioms successful_return_control
#print axioms failed_return_not_success
#print axioms hit_control
#print axioms miss_control
#print axioms old_answer_not_appended
#print axioms saved_frame_control
#print axioms repeated_entry_control
end ExplainableCrypto.Helios.Computational.CacheCallerMachineControls
