import ExplainableCrypto.Helios.Computational.PrimeSimDifferenceMachine

namespace ExplainableCrypto.Helios.Computational.PrimeSimDifferenceMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 400000

def retained (old : Fin 39 → List Bool) : Fin 29 → List Bool :=
  ![old 0,old 3,old 4,old 5,old 6,old 7,old 8,old 9,old 12,old 13,old 14,old 15,old 16,old 17,old 18,old 19,old 20,old 21,old 22,old 29,old 30,old 31,old 32,old 33,old 34,old 35,old 36,old 37,old 38]

/-- Both scalar prefixes and every blank work word follow from the actual
completed zero-branch caller; no structural presentation is supplied. -/
theorem source_inputs {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    let old := PrimeSimCommitPairCaller.sourceResult slack g pk vote saved out
    BitOracleStackFrame.embed layout
      (ScalarDifferenceMachine.start q.bits (uniformNatEncode out.2.1.val)
        (uniformNatEncode out.2.2.1.val)) (retained old.stk) = start old.stk := by
  dsimp only
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl

/-- The original39-word result changes only its previously empty d-prefix
port; all temporary arithmetic/decoder work is restored empty. -/
theorem source_outputs {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q))
    (answer : List Bool) :
    let old := PrimeSimCommitPairCaller.sourceResult slack g pk vote saved out
    BitOracleStackFrame.embed layout
      (ScalarDifferenceMachine.result q.bits (uniformNatEncode out.2.1.val)
        (uniformNatEncode out.2.2.1.val) answer) (retained old.stk) =
    result answer old.stk := by
  dsimp only
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl

#print axioms source_inputs
#print axioms source_outputs
end ExplainableCrypto.Helios.Computational.PrimeSimDifferenceMachine
