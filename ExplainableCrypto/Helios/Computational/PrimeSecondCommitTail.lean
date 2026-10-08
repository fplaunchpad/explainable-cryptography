import ExplainableCrypto.Helios.Computational.PrimeSecondCommitBMachine
import ExplainableCrypto.Helios.Computational.PrimeSecondDifferenceMachine
import ExplainableCrypto.Helios.Computational.PrimeSecondAdjustedMachine
import ExplainableCrypto.Helios.Computational.PrimeSecondOneFirstMachine
import ExplainableCrypto.Helios.Computational.PrimeSecondOneSecondMachine

namespace ExplainableCrypto.Helios.Computational.PrimeSecondCommitTail
open OracleComp OracleSpec BitOracleMachine
set_option maxRecDepth 65536

def size : Nat := 1975
instance : NeZero size := ⟨by decide⟩
def bLayout : Fin 66 ⊕ Fin 4 ≃ Fin 70 := finSumFinEquiv
def bCode : Code 70 PrimeSecondCommitBMachine.size 3 :=
  BitOracleStackFrame.code bLayout PrimeSecondCommitBMachine.code
def bLabel (l : Fin PrimeSecondCommitBMachine.size) : Fin size :=
  ⟨0+l.val,by have := l.isLt; change l.val < 543 at this; unfold size; omega⟩
def differenceLayout : Fin 67 ⊕ Fin 3 ≃ Fin 70 := finSumFinEquiv
def differenceCode : Code 70 PrimeSecondDifferenceMachine.size 3 :=
  BitOracleStackFrame.code differenceLayout PrimeSecondDifferenceMachine.code
def differenceLabel (l : Fin PrimeSecondDifferenceMachine.size) : Fin size :=
  ⟨543+l.val,by have := l.isLt; change l.val < 66 at this; unfold size; omega⟩
def adjustedLayout : Fin 68 ⊕ Fin 2 ≃ Fin 70 := finSumFinEquiv
def adjustedCode : Code 70 PrimeSecondAdjustedMachine.size 3 :=
  BitOracleStackFrame.code adjustedLayout PrimeSecondAdjustedMachine.code
def adjustedLabel (l : Fin PrimeSecondAdjustedMachine.size) : Fin size :=
  ⟨609+l.val,by have := l.isLt; change l.val < 280 at this; unfold size; omega⟩
def firstLayout : Fin 69 ⊕ Fin 1 ≃ Fin 70 := finSumFinEquiv
def firstCode : Code 70 PrimeSecondOneFirstMachine.size 3 :=
  BitOracleStackFrame.code firstLayout PrimeSecondOneFirstMachine.code
def firstLabel (l : Fin PrimeSecondOneFirstMachine.size) : Fin size :=
  ⟨889+l.val,by have := l.isLt; change l.val < 543 at this; unfold size; omega⟩
def secondCode : Code 70 PrimeSecondOneSecondMachine.size 3 := PrimeSecondOneSecondMachine.code
def secondLabel (l : Fin PrimeSecondOneSecondMachine.size) : Fin size :=
  ⟨1432+l.val,by have := l.isLt; change l.val < 543 at this; unfold size; omega⟩

def code (l : Fin size) : Command 70 size 3 :=
  if h : l.val < 543 then BitOracleReturnLink.command bLabel (some (differenceLabel 0))
    (bCode ⟨l.val-0,by change l.val-0 < 543; omega⟩)
  else if h : l.val < 609 then BitOracleReturnLink.command differenceLabel (some (adjustedLabel 0))
    (differenceCode ⟨l.val-543,by change l.val-543 < 66; omega⟩)
  else if h : l.val < 889 then BitOracleReturnLink.command adjustedLabel (some (firstLabel 0))
    (adjustedCode ⟨l.val-609,by change l.val-609 < 280; omega⟩)
  else if h : l.val < 1432 then BitOracleReturnLink.command firstLabel (some (secondLabel 0))
    (firstCode ⟨l.val-889,by change l.val-889 < 543; omega⟩)
  else BitOracleReturnLink.command secondLabel none
    (secondCode ⟨l.val-1432,by have := l.isLt; unfold size at this; change l.val-1432 < 543; omega⟩)
abbrev Config := BitOracleMachine.Config 70 size 3
def start (old : Fin 65 → List Bool) : Config :=
  BitOracleReturnLink.embed bLabel (some (differenceLabel 0))
    (BitOracleStackFrame.embed bLayout (PrimeSecondCommitBMachine.start old) (fun _ => []))
def clock (p q : Nat) :=
  PrimeSecondCommitBMachine.clock p q + (PrimeSecondDifferenceMachine.clock q +
    (PrimeSecondAdjustedMachine.clock p q +
      (PrimeSecondOneFirstMachine.clock p q + PrimeSecondOneSecondMachine.clock p q)))
def cost (p q : Nat) :=
  PrimeSecondCommitBMachine.cost p q + (PrimeSecondDifferenceMachine.cost q +
    (PrimeSecondAdjustedMachine.cost p q +
      (PrimeSecondOneFirstMachine.cost p q + PrimeSecondOneSecondMachine.cost p q)))

theorem b_code (l : Fin PrimeSecondCommitBMachine.size) : code (bLabel l) =
    BitOracleReturnLink.command bLabel (some (differenceLabel 0)) (bCode l) := by
  have hi : (bLabel l).val < 543 := by
    dsimp [bLabel]; have := l.isLt; change l.val < 543 at this; omega
  simp only [code,dif_pos hi]
  simp only [bLabel,Nat.add_sub_cancel_left]

theorem difference_code (l : Fin PrimeSecondDifferenceMachine.size) : code (differenceLabel l) =
    BitOracleReturnLink.command differenceLabel (some (adjustedLabel 0)) (differenceCode l) := by
  have h0 : ¬ (differenceLabel l).val < 543 := by dsimp [differenceLabel]; omega
  have hi : (differenceLabel l).val < 609 := by
    dsimp [differenceLabel]; have := l.isLt; change l.val < 66 at this; omega
  simp only [code,dif_neg h0,dif_pos hi]
  simp only [differenceLabel,Nat.add_sub_cancel_left]

theorem adjusted_code (l : Fin PrimeSecondAdjustedMachine.size) : code (adjustedLabel l) =
    BitOracleReturnLink.command adjustedLabel (some (firstLabel 0)) (adjustedCode l) := by
  have h0 : ¬ (adjustedLabel l).val < 543 := by dsimp [adjustedLabel]; omega
  have h1 : ¬ (adjustedLabel l).val < 609 := by dsimp [adjustedLabel]; omega
  have hi : (adjustedLabel l).val < 889 := by
    dsimp [adjustedLabel]; have := l.isLt; change l.val < 280 at this; omega
  simp only [code,dif_neg h0,dif_neg h1,dif_pos hi]
  simp only [adjustedLabel,Nat.add_sub_cancel_left]

theorem first_code (l : Fin PrimeSecondOneFirstMachine.size) : code (firstLabel l) =
    BitOracleReturnLink.command firstLabel (some (secondLabel 0)) (firstCode l) := by
  have h0 : ¬ (firstLabel l).val < 543 := by dsimp [firstLabel]; omega
  have h1 : ¬ (firstLabel l).val < 609 := by dsimp [firstLabel]; omega
  have h2 : ¬ (firstLabel l).val < 889 := by dsimp [firstLabel]; omega
  have hi : (firstLabel l).val < 1432 := by
    dsimp [firstLabel]; have := l.isLt; change l.val < 543 at this; omega
  simp only [code,dif_neg h0,dif_neg h1,dif_neg h2,dif_pos hi]
  simp only [firstLabel,Nat.add_sub_cancel_left]

theorem second_code (l : Fin PrimeSecondOneSecondMachine.size) : code (secondLabel l) =
    BitOracleReturnLink.command secondLabel none (secondCode l) := by
  have h0 : ¬ (secondLabel l).val < 543 := by dsimp [secondLabel]; omega
  have h1 : ¬ (secondLabel l).val < 609 := by dsimp [secondLabel]; omega
  have h2 : ¬ (secondLabel l).val < 889 := by dsimp [secondLabel]; omega
  have h3 : ¬ (secondLabel l).val < 1432 := by dsimp [secondLabel]; omega
  simp only [code,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3]
  simp only [secondLabel,Nat.add_sub_cancel_left]

/-- The successful b return supplies the next entry with the same resident
words and blank remaining outputs; no data reconstruction is assumed. -/
theorem b_return (old : Fin 66 → List Bool) :
    BitOracleReturnLink.embed bLabel (some (differenceLabel 0))
      (BitOracleStackFrame.embed bLayout
        (⟨none,2,old⟩ : PrimeSecondCommitBMachine.Config) (fun _ => [])) =
    BitOracleReturnLink.embed differenceLabel (some (adjustedLabel 0))
      (BitOracleStackFrame.embed differenceLayout (PrimeSecondDifferenceMachine.start old) (fun _ => [])) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

/-- The successful difference return supplies the next entry with the same resident
words and blank remaining outputs; no data reconstruction is assumed. -/
theorem difference_return (old : Fin 67 → List Bool) :
    BitOracleReturnLink.embed differenceLabel (some (adjustedLabel 0))
      (BitOracleStackFrame.embed differenceLayout
        (⟨none,2,old⟩ : PrimeSecondDifferenceMachine.Config) (fun _ => [])) =
    BitOracleReturnLink.embed adjustedLabel (some (firstLabel 0))
      (BitOracleStackFrame.embed adjustedLayout (PrimeSecondAdjustedMachine.start old) (fun _ => [])) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

/-- The successful adjusted return supplies the next entry with the same resident
words and blank remaining outputs; no data reconstruction is assumed. -/
theorem adjusted_return (old : Fin 68 → List Bool) :
    BitOracleReturnLink.embed adjustedLabel (some (firstLabel 0))
      (BitOracleStackFrame.embed adjustedLayout
        (⟨none,2,old⟩ : PrimeSecondAdjustedMachine.Config) (fun _ => [])) =
    BitOracleReturnLink.embed firstLabel (some (secondLabel 0))
      (BitOracleStackFrame.embed firstLayout (PrimeSecondOneFirstMachine.start old) (fun _ => [])) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

/-- The successful first return supplies the next entry with the same resident
words and blank remaining outputs; no data reconstruction is assumed. -/
theorem first_return (old : Fin 69 → List Bool) :
    BitOracleReturnLink.embed firstLabel (some (secondLabel 0))
      (BitOracleStackFrame.embed firstLayout
        (⟨none,2,old⟩ : PrimeSecondOneFirstMachine.Config) (fun _ => [])) =
    BitOracleReturnLink.embed secondLabel none
      (PrimeSecondOneSecondMachine.start old) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

#print axioms b_return
#print axioms difference_return
#print axioms adjusted_return
#print axioms first_return

#print axioms b_code
#print axioms difference_code
#print axioms adjusted_code
#print axioms first_code
#print axioms second_code
end ExplainableCrypto.Helios.Computational.PrimeSecondCommitTail
