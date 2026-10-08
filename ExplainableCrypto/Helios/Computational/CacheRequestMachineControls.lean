import ExplainableCrypto.Helios.Computational.CacheRequestMachineRun

/-! Kernel controls for the serialized-input request wrapper. Scalar digits,
coin consumption and chronological log order are fixed independently of the
wrapper. Rejection controls pin the actual guard and minimized framing failures. -/
namespace ExplainableCrypto.Helios.Computational.CacheRequestMachineControls
open OracleComp OracleSpec BitOracleMachine CacheRequestMachine BallotCacheCodecControls
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
set_option maxRecDepth 8192

private def handler : QueryImpl spec (StateT (List Bool) Id) := fun r tape =>
  match r with
  | .coin => (tape.headD false,tape.tail)
  | .hash word => (word,tape)

/-- Observe the actual wrapper from its single serialized input word. -/
def trace (c : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11))
    (log : List (Unit × BallotForkPoint (PrimeGroup 23 11))) (slack : Nat) (tape : List Bool) :
    Config 12 size 3 × List Bool :=
  (simulateQ handler (Prod.fst <$> run code (clock c key log slack)
    (start (input c key log slack)))).run tape

private theorem trace_eq (c : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11))
    (log : List (Unit × BallotForkPoint (PrimeGroup 23 11))) (slack : Nat) (tape : List Bool) :
    trace c log slack tape = (simulateQ handler
      (BitOracleReturnLink.embed requestLabel none <$> CacheHashDispatch.request c key log slack)).run tape := by
  unfold trace
  rw [(request_run c key log slack).1]

/-- A stored three returns the canonical prefix 11011, leaves the old log intact,
and consumes none of the supplied coins after parsing the serialized input. -/
theorem hit_control : trace cache [((),otherKey)] 2 [true,false,true] =
    (BitOracleReturnLink.embed requestLabel none
      (CacheHashDispatch.result ((ballotKeyBitCodec 23 11).encode key)
        ((ballotCacheBitCodec 23 11).encode cache)
        (((ballotLogEntryBitCodec 23 11).list).encode [((),otherKey)])
        (SamplerOperands.input 2 11 []) [true,true,false,true,true]),[true,false,true]) := by
  rw [trace_eq]
  have found : cache.lookup key = some 3 := by decide +kernel
  rw [CacheHashDispatch.request,found]
  rfl

/-- Chronological coin bits 0110 represent six. Four bits are consumed, six is
inserted, and the queried key follows the pre-existing chronological log entry. -/
theorem miss_control : trace ∅ [((),otherKey)] 0 [false,true,true,false,true] =
    (BitOracleReturnLink.embed requestLabel none
      (CacheHashDispatch.result ((ballotKeyBitCodec 23 11).encode key)
        ((ballotCacheBitCodec 23 11).encode
          ((∅ : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11)).insert key 6))
        (((ballotLogEntryBitCodec 23 11).list).encode [((),otherKey),((),key)])
        (SamplerOperands.input 0 11 []) [true,true,true,false,false,true,true]),[true]) := by
  rw [trace_eq]
  rfl

/-- Zero is a valid sampled scalar with the one-bit prefix 0, rather than a
malformed or rejected value. The final true coin remains unused. -/
theorem zero_control : trace ∅ [] 0 [false,false,false,false,true] =
    (BitOracleReturnLink.embed requestLabel none
      (CacheHashDispatch.result ((ballotKeyBitCodec 23 11).encode key)
        ((ballotCacheBitCodec 23 11).encode
          ((∅ : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11)).insert key 0))
        (((ballotLogEntryBitCodec 23 11).list).encode [((),key)])
        (SamplerOperands.input 0 11 []) [false]),[true]) := by
  rw [trace_eq]
  rfl

/-- Eagerly sampling a cache hit would incorrectly consume the first true coin. -/
theorem hit_not_sampled : (trace cache [((),otherKey)] 2 [true,false,true]).2 ≠ [false,true] := by
  rw [hit_control]
  decide +kernel

/-- The actual raw-input miss distinguishes six from constant-zero sampling. -/
theorem miss_not_zero : (trace ∅ [((),otherKey)] 0 [false,true,true,false,true]).1.stk 7 ≠ [false] := by
  rw [miss_control]
  decide +kernel

/-- Prepending the new request would change the returned chronological log. -/
theorem log_not_prepend : (trace ∅ [((),otherKey)] 0 [false,true,true,false,true]).1.stk 10 ≠
    (((ballotLogEntryBitCodec 23 11).list).encode [((),key),((),otherKey)]) := by
  rw [miss_control]
  decide +kernel

/-- The completed serialized request clears work while retaining the full key
and private sampler record. All these ports come from the actual wrapper run. -/
theorem miss_frame_control :
    let out := (trace ∅ [((),otherKey)] 0 [false,true,true,false,true]).1
    (∀ k : Fin 7, out.stk ⟨k.val,by omega⟩ = []) ∧
      out.stk 8 = (ballotKeyBitCodec 23 11).encode key ∧
      out.stk 11 = SamplerOperands.input 0 11 [] := by
  rw [miss_control]
  refine ⟨?_,rfl,rfl⟩
  intro k
  fin_cases k <;> rfl

/-- A rejected parser return cannot enter the dispatcher, even when all useful
payload ports have already been filled. The guard preserves every word. -/
theorem rejected_gate_control (words : Fin 12 → List Bool) :
    BitOracleMachine.step code ⟨some gateLabel,0,words⟩ =
      pure ((⟨none,0,words⟩ : Config 12 size 3),3) := by
  rfl

/-- Observe the control successor, independently of the charge: unconditionally
entering the dispatcher after failed parsing is not this wrapper's behavior. -/
theorem rejected_gate_not_dispatched (words : Fin 12 → List Bool) :
    (fun out => out.1.l) <$> BitOracleMachine.step code ⟨some gateLabel,0,words⟩ ≠
      pure (some (requestLabel 0)) := by
  rw [rejected_gate_control]
  simp

/-- Minimized absent fourth-field fixture: count four followed by only three
empty fields. Actual parsing and the wrapper gate both reject. -/
theorem missing_fourth_field_control :
    run code 36 (start [true,true,true,false,false,false,true,false,false,false]) =
      pure ((⟨none,0,fun _ => []⟩ : Config 12 size 3),136) := by
  change (pure ((⟨_,_,_⟩ : Config 12 size 3),136) : OracleComp spec (Config 12 size 3 × Nat)) = _
  congr 2
  change (⟨_,_,_⟩ : Config 12 size 3) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

/-- Minimized trailing-suffix fixture: four empty fields followed by one extra
false bit. Rejection retains that unread bit on input port 6. -/
theorem trailing_suffix_control :
    run code 42 (start [true,true,true,false,false,false,true,false,false,false,false,false]) =
      pure ((⟨none,0,![[],[],[],[],[],[],[false],[],[],[],[],[]]⟩ : Config 12 size 3),161) := by
  change (pure ((⟨_,_,_⟩ : Config 12 size 3),161) : OracleComp spec (Config 12 size 3 × Nat)) = _
  congr 2
  change (⟨_,_,_⟩ : Config 12 size 3) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

#print axioms hit_control
#print axioms miss_control
#print axioms zero_control
#print axioms hit_not_sampled
#print axioms miss_not_zero
#print axioms log_not_prepend
#print axioms miss_frame_control
#print axioms rejected_gate_control
#print axioms rejected_gate_not_dispatched
#print axioms missing_fourth_field_control
#print axioms trailing_suffix_control
end ExplainableCrypto.Helios.Computational.CacheRequestMachineControls
