import ExplainableCrypto.Helios.Computational.PrimeSimCommitCaller
import ExplainableCrypto.Helios.Computational.PrimeSimCommitMachineSource

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitCaller
open OracleComp OracleSpec BitOracleMachine

def entry : Fin size := prefixLabel (PrimeHonestTranscriptCaller.cipherLabel
  (PrimeHonestCiphertextMachine.inputLabel (PrimeHonestInputMachine.copyLabel 0)))

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
  · have h := Finset.le_sup (f := fun k : Fin 38 =>
      ((BitOracleInitialInput.source (7 : Fin 38) (some entry) (0 : Fin 3) raw).stk k).length)
      (Finset.mem_univ (7 : Fin 38))
    simpa [BitOracleInitialInput.source] using h

/-- The typed source's actual returned frame gives the concrete commitment
operands. This discharges presentation from the existing reached-state theorem. -/
theorem source_return {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    let old := PrimeHonestTranscriptCaller.sourceResult slack g pk vote saved out
    BitOracleReturnLink.embed prefixLabel (some (commitLabel 0))
      (BitOracleStackFrame.embed prefixLayout old (fun _ => [])) =
    BitOracleReturnLink.embed commitLabel none
      (PrimeSimCommitMachine.start (PrimeSimCommitMachine.inputWords p q (primeGroupCoordinate g).val
        (primeGroupCoordinate (encryptWith g pk out.1.1 (voteScalar vote)).1).val
        out.2.2.1.val out.2.2.2.1.val
        ![old.stk 0,old.stk 7,old.stk 10,old.stk 13,old.stk 14,old.stk 15,
          old.stk 18,old.stk 19,old.stk 20,old.stk 21,old.stk 22])) := by
  dsimp only
  rw [PrimeSimCommitMachine.inputWords_source]
  exact prefix_return _

#print axioms start_source
#print axioms start_height
#print axioms source_return
end ExplainableCrypto.Helios.Computational.PrimeSimCommitCaller
