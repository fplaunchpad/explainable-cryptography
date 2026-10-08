import ExplainableCrypto.Helios.Computational.PrimeSimOneFirstMachine

namespace ExplainableCrypto.Helios.Computational.PrimeSimOneFirstMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 400000

def retained (old : Fin 40 → List Bool) : Fin 11 → List Bool :=
  ![old 0,old 11,old 10,old 13,old 14,old 15,old 18,old 19,old 20,old 21,old 22]

/-- The reached adjusted-beta source supplies actual g/alpha, d/z1 prefixes,
blank scratch and all four words in the complementary frame. -/
theorem source_inputs {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    let old := PrimeAdjustedBetaMachine.sourceResult slack g pk vote saved out
    BitOracleStackFrame.embed layout
      (PrimeSimCommitMachine.start (PrimeSimCommitMachine.inputWords p q
        (primeGroupCoordinate g).val
        (primeGroupCoordinate (encryptWith g pk out.1.1 (voteScalar vote)).1).val
        (out.2.1-out.2.2.1).val out.2.2.2.2.val (retained old.stk)))
      ![old.stk 3,old.stk 12,old.stk 38,old.stk 39] = start old.stk := by
  dsimp only
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

/-- Every original word is retained, including d and all three prior coordinates.
Only new port40 receives the first one-branch answer; scratch41 is empty. -/
theorem source_outputs {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q))
    (answer : List Bool) :
    let old := PrimeAdjustedBetaMachine.sourceResult slack g pk vote saved out
    BitOracleStackFrame.embed layout
      (PrimeSimCommitMachine.result answer (PrimeSimCommitMachine.inputWords p q
        (primeGroupCoordinate g).val
        (primeGroupCoordinate (encryptWith g pk out.1.1 (voteScalar vote)).1).val
        (out.2.1-out.2.2.1).val out.2.2.2.2.val (retained old.stk)))
      ![old.stk 3,old.stk 12,old.stk 38,old.stk 39] = result answer old.stk := by
  dsimp only
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

#print axioms source_inputs
#print axioms source_outputs
end ExplainableCrypto.Helios.Computational.PrimeSimOneFirstMachine
