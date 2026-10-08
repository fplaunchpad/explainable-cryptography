import ExplainableCrypto.Helios.Computational.PrimeSimCommitPairCaller
import ExplainableCrypto.Helios.Computational.PrimeSimCommitSecondMachineSource

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitPairCaller
open OracleComp OracleSpec BitOracleMachine

def entry : Fin size := prefixLabel PrimeSimCommitCaller.entry

/-- The only initialized word is the user's original encoded private input;
framing does not add prepared operands or a ready-state certificate. -/
theorem start_source (raw : List Bool) :
    start raw = BitOracleInitialInput.source 7 (some entry) 0 raw := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl

theorem start_height (raw : List Bool) : TM2TapeRuns.height (start raw).stk = raw.length := by
  rw [start_source]
  unfold TM2TapeRuns.height
  apply le_antisymm
  · apply Finset.sup_le
    intro k _
    by_cases h : k = 7
    · subst k; simp [BitOracleInitialInput.source]
    · simp [BitOracleInitialInput.source,Function.update,h]
  · have h := Finset.le_sup (f := fun k : Fin 39 =>
      ((BitOracleInitialInput.source (7 : Fin 39) (some entry) (0 : Fin 3) raw).stk k).length)
      (Finset.mem_univ (7 : Fin 39))
    simpa [BitOracleInitialInput.source] using h

/-- The actual typed predecessor enters the second-coordinate controller with
its complete returned state, including the retained first coordinate. -/
theorem source_return {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    let old := PrimeSimCommitCaller.sourceResult slack g pk vote saved out
    BitOracleReturnLink.embed prefixLabel (some (commitLabel 0))
      (BitOracleStackFrame.embed prefixLayout old (fun _ => [])) =
    BitOracleReturnLink.embed commitLabel none (PrimeSimCommitSecondMachine.start old.stk) := by
  exact prefix_return _

#print axioms source_return
#print axioms start_source
#print axioms start_height
end ExplainableCrypto.Helios.Computational.PrimeSimCommitPairCaller
