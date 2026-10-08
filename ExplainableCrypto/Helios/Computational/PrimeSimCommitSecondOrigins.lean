import ExplainableCrypto.Helios.Computational.PrimeSimCommitSecondMachine

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitSecondMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 400000

def retained (old : Fin 38 → List Bool) : Fin 11 → List Bool :=
  ![old 17,old 7,old 10,old 13,old 14,old 16,old 18,old 19,old 20,old 21,old 22]

/-- The original first-coordinate source result supplies pk/beta, scalar words,
blank scratch and the first result in the singleton frame. -/
theorem source_inputs {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    let old := PrimeSimCommitCaller.sourceResult slack g pk vote saved out
    BitOracleStackFrame.embed layout
      (PrimeSimCommitMachine.start (PrimeSimCommitMachine.inputWords p q
        (primeGroupCoordinate pk).val
        (primeGroupCoordinate (encryptWith g pk out.1.1 (voteScalar vote)).2).val
        out.2.2.1.val out.2.2.2.1.val (retained old.stk)))
      (fun _ => old.stk 3) = start old.stk := by
  dsimp only
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

/-- Every original word is retained, including first coordinate3. Only the new
port38 receives the second answer; all existing power work ports remain empty. -/
theorem source_outputs {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q))
    (answer : List Bool) :
    let old := PrimeSimCommitCaller.sourceResult slack g pk vote saved out
    BitOracleStackFrame.embed layout
      (PrimeSimCommitMachine.result answer (PrimeSimCommitMachine.inputWords p q
        (primeGroupCoordinate pk).val
        (primeGroupCoordinate (encryptWith g pk out.1.1 (voteScalar vote)).2).val
        out.2.2.1.val out.2.2.2.1.val (retained old.stk)))
      (fun _ => old.stk 3) = result answer old.stk := by
  dsimp only
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

#print axioms source_inputs
#print axioms source_outputs
end ExplainableCrypto.Helios.Computational.PrimeSimCommitSecondMachine
