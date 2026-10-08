import ExplainableCrypto.Helios.Computational.PrimeSimKeyMachineRun
import ExplainableCrypto.Helios.Computational.PrimeSimKeySource

namespace ExplainableCrypto.Helios.Computational.PrimeSimKeyMachine
open OracleComp BitOracleMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
attribute [local irreducible] BitOracleMachine.run

/-- Reverse execution order of the actual eight typed key coordinates. -/
def sourceValues {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (vote : Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) : Fin 8 → Nat :=
  let k := PrimeSimKeySource.key g pk vote out
  fun i => (primeGroupCoordinate
    (![k.2.2.2,k.2.2.1,k.2.1.2,k.2.1.1,k.1.ciphertext.2,k.1.ciphertext.1,
      k.1.publicKey,k.1.generator] i)).val

/-- Complete previous state with the original cache-key codec on the new port. -/
def sourceResult {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) : Config :=
  result ((ballotKeyBitCodec p q).encode (PrimeSimKeySource.key g pk vote out))
    (PrimeSimAllCommitCaller.sourceResult slack g pk vote saved out).stk

theorem source_values {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) (i : Fin 8) :
    (PrimeSimAllCommitCaller.sourceResult slack g pk vote saved out).stk (sourcePort i) =
      (sourceValues g pk vote out i).bits := by
  fin_cases i <;> rfl

theorem source_encoding {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (vote : Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    encoded (sourceValues g pk vote out) =
      (ballotKeyBitCodec p q).encode (PrimeSimKeySource.key g pk vote out) := rfl

/-- Every operand, width and workspace condition is derived from the actual
completed commitment state. No encoded-key or frame premise is supplied. -/
theorem charged_source {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    ∃ charge ≤ cost p,
      BitOracleMachine.run code (clock p)
        (start (PrimeSimAllCommitCaller.sourceResult slack g pk vote saved out).stk) =
          pure (sourceResult slack g pk vote saved out,charge) := by
  obtain ⟨charge,hc,he⟩ := charged p (sourceValues g pk vote out)
    (PrimeSimAllCommitCaller.sourceResult slack g pk vote saved out).stk
    (PrimeSimKeySource.source_work slack g pk vote saved out)
    (source_values slack g pk vote saved out)
    (fun i => (primeGroupCoordinate _).val_lt)
  exact ⟨charge,hc,he⟩

theorem source {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    Prod.fst <$> BitOracleMachine.run code (clock p)
      (start (PrimeSimAllCommitCaller.sourceResult slack g pk vote saved out).stk) =
        pure (sourceResult slack g pk vote saved out) := by
  obtain ⟨charge,_,he⟩ := charged_source slack g pk vote saved out
  rw [he]
  simp

#print axioms source_values
#print axioms source_encoding
#print axioms charged_source
#print axioms source
end ExplainableCrypto.Helios.Computational.PrimeSimKeyMachine
