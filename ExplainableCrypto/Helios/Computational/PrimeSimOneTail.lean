import ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachineSource
import ExplainableCrypto.Helios.Computational.PrimeSimOneFirstMachine
import ExplainableCrypto.Helios.Computational.PrimeSimOneSecondMachine

namespace ExplainableCrypto.Helios.Computational.PrimeSimOneTail
open OracleComp OracleSpec BitOracleMachine

def size : Nat := 1366
instance : NeZero size := ⟨by decide⟩
def betaLayout : Fin 40 ⊕ Fin 3 ≃ Fin 43 := finSumFinEquiv
def firstLayout : Fin 42 ⊕ Fin 1 ≃ Fin 43 := finSumFinEquiv
def betaCode : Code 43 PrimeAdjustedBetaMachine.size 3 :=
  BitOracleStackFrame.code betaLayout PrimeAdjustedBetaMachine.code
def firstCode : Code 43 PrimeSimOneFirstMachine.size 3 :=
  BitOracleStackFrame.code firstLayout PrimeSimOneFirstMachine.code
def betaLabel (l : Fin PrimeAdjustedBetaMachine.size) : Fin size :=
  ⟨l.val,by have := l.isLt; change l.val < 280 at this; unfold size; omega⟩
def firstLabel (l : Fin PrimeSimOneFirstMachine.size) : Fin size :=
  ⟨280+l.val,by have := l.isLt; change l.val < 543 at this; unfold size; omega⟩
def secondLabel (l : Fin PrimeSimOneSecondMachine.size) : Fin size :=
  ⟨823+l.val,by have := l.isLt; change l.val < 543 at this; unfold size; omega⟩
def code (l : Fin size) : Command 43 size 3 :=
  if h : l.val < 280 then BitOracleReturnLink.command betaLabel (some (firstLabel 0))
    (betaCode ⟨l.val,h⟩)
  else if h : l.val < 823 then BitOracleReturnLink.command firstLabel (some (secondLabel 0))
    (firstCode ⟨l.val-280,by change l.val-280 < 543; omega⟩)
  else BitOracleReturnLink.command secondLabel none
    (PrimeSimOneSecondMachine.code ⟨l.val-823,by have := l.isLt; unfold size at this; change l.val-823 < 543; omega⟩)
abbrev Config := BitOracleMachine.Config 43 size 3
def start (old : Fin 39 → List Bool) : Config :=
  BitOracleReturnLink.embed betaLabel (some (firstLabel 0))
    (BitOracleStackFrame.embed betaLayout (PrimeAdjustedBetaMachine.start old) (fun _ => []))
def clock (p q : Nat) := PrimeAdjustedBetaMachine.clock p q+2*PrimeSimCommitMachine.clock p q
def cost (p q : Nat) := PrimeAdjustedBetaMachine.cost p q+2*PrimeSimCommitMachine.cost p q

theorem beta_code (l : Fin PrimeAdjustedBetaMachine.size) : code (betaLabel l) =
    BitOracleReturnLink.command betaLabel (some (firstLabel 0)) (betaCode l) := by
  have h : (betaLabel l).val < 280 := l.isLt
  simp only [code,dif_pos h]
  rfl

theorem first_code (l : Fin PrimeSimOneFirstMachine.size) : code (firstLabel l) =
    BitOracleReturnLink.command firstLabel (some (secondLabel 0)) (firstCode l) := by
  have h0 : ¬ (firstLabel l).val < 280 := by dsimp [firstLabel]; omega
  have h1 : (firstLabel l).val < 823 := by dsimp [firstLabel]; have := l.isLt; change l.val < 543 at this; omega
  simp only [code,dif_neg h0,dif_pos h1]
  simp only [firstLabel,Nat.add_sub_cancel_left]

theorem second_code (l : Fin PrimeSimOneSecondMachine.size) : code (secondLabel l) =
    BitOracleReturnLink.command secondLabel none (PrimeSimOneSecondMachine.code l) := by
  have h0 : ¬ (secondLabel l).val < 280 := by dsimp [secondLabel]; omega
  have h1 : ¬ (secondLabel l).val < 823 := by dsimp [secondLabel]; omega
  simp only [code,dif_neg h0,dif_neg h1]
  simp only [secondLabel,Nat.add_sub_cancel_left]

#print axioms beta_code
#print axioms first_code
#print axioms second_code
end ExplainableCrypto.Helios.Computational.PrimeSimOneTail
