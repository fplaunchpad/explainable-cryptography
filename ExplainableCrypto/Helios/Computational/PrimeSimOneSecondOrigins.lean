import ExplainableCrypto.Helios.Computational.PrimeSimOneSecondMachine
import ExplainableCrypto.Helios.Computational.PrimeSimOneFirstMachineSource

namespace ExplainableCrypto.Helios.Computational.PrimeSimOneSecondMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 400000

def retained (old : Fin 42 → List Bool) : Fin 11 → List Bool :=
  ![old 0,old 11,old 10,old 13,old 14,old 16,old 18,old 19,old 20,old 21,old 22]

/-- The actual first one-branch source supplies pk/adjusted-beta, scalar words,
blank scratch and the three earlier coordinates in the five-word frame. -/
theorem source_inputs {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    let old := PrimeSimOneFirstMachine.sourceResult slack g pk vote saved out
    BitOracleStackFrame.embed layout
      (PrimeSimCommitMachine.start (PrimeSimCommitMachine.inputWords p q
        (primeGroupCoordinate pk).val
        (primeGroupCoordinate ((encryptWith g pk out.1.1 (voteScalar vote)).2-g)).val
        (out.2.1-out.2.2.1).val out.2.2.2.2.val (retained old.stk)))
      ![old.stk 3,old.stk 12,old.stk 17,old.stk 38,old.stk 40] = start old.stk := by
  dsimp only
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

/-- Every original word is retained, including the three earlier commitment coordinates. Only new
port42 receives the fourth answer; all existing power work ports remain empty. -/
theorem source_outputs {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q))
    (answer : List Bool) :
    let old := PrimeSimOneFirstMachine.sourceResult slack g pk vote saved out
    BitOracleStackFrame.embed layout
      (PrimeSimCommitMachine.result answer (PrimeSimCommitMachine.inputWords p q
        (primeGroupCoordinate pk).val
        (primeGroupCoordinate ((encryptWith g pk out.1.1 (voteScalar vote)).2-g)).val
        (out.2.1-out.2.2.1).val out.2.2.2.2.val (retained old.stk)))
      ![old.stk 3,old.stk 12,old.stk 17,old.stk 38,old.stk 40] = result answer old.stk := by
  dsimp only
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

#print axioms source_inputs
#print axioms source_outputs
end ExplainableCrypto.Helios.Computational.PrimeSimOneSecondMachine
