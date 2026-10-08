import ExplainableCrypto.Helios.Computational.PrimeSimDifferenceMachine

namespace ExplainableCrypto.Helios.Computational.PrimeSimDifferenceCaller
open OracleComp OracleSpec BitOracleMachine

def size : Nat := 2118
instance : NeZero size := ⟨by decide⟩
def prefixLabel (l : Fin PrimeSimCommitPairCaller.size) : Fin size :=
  ⟨l.val,by have := l.isLt; unfold PrimeSimCommitPairCaller.size at this; unfold size; omega⟩
def differenceLabel (l : Fin PrimeSimDifferenceMachine.size) : Fin size :=
  ⟨2052+l.val,by have := l.isLt; change l.val < 66 at this; unfold size; omega⟩
def code (l : Fin size) : Command 39 size 3 :=
  if h : l.val < 2052 then
    BitOracleReturnLink.command prefixLabel (some (differenceLabel 0))
      (PrimeSimCommitPairCaller.code ⟨l.val,h⟩)
  else BitOracleReturnLink.command differenceLabel none
    (PrimeSimDifferenceMachine.code ⟨l.val-2052,by have := l.isLt; unfold size at this; change l.val-2052 < 66; omega⟩)
abbrev Config := BitOracleMachine.Config 39 size 3
def start (raw : List Bool) : Config :=
  BitOracleReturnLink.embed prefixLabel (some (differenceLabel 0)) (PrimeSimCommitPairCaller.start raw)
def clock (raw : List Bool) (slack p q : Nat) :=
  PrimeSimCommitPairCaller.clock raw slack p q+PrimeSimDifferenceMachine.clock q
def cost (raw : List Bool) (slack p q : Nat) :=
  PrimeSimCommitPairCaller.cost raw slack p q+PrimeSimDifferenceMachine.cost q

theorem prefix_code (l : Fin PrimeSimCommitPairCaller.size) : code (prefixLabel l) =
    BitOracleReturnLink.command prefixLabel (some (differenceLabel 0)) (PrimeSimCommitPairCaller.code l) := by
  have h : (prefixLabel l).val < 2052 := l.isLt
  simp only [code,dif_pos h]
  rfl

theorem difference_code (l : Fin PrimeSimDifferenceMachine.size) : code (differenceLabel l) =
    BitOracleReturnLink.command differenceLabel none (PrimeSimDifferenceMachine.code l) := by
  have h : ¬ (differenceLabel l).val < 2052 := by dsimp [differenceLabel]; omega
  simp only [code,dif_neg h]
  simp only [differenceLabel,Nat.add_sub_cancel_left]

theorem prefix_return (original : Fin 39 → List Bool) :
    BitOracleReturnLink.embed prefixLabel (some (differenceLabel 0))
      (⟨none,2,original⟩ : PrimeSimCommitPairCaller.Config) =
    BitOracleReturnLink.embed differenceLabel none (PrimeSimDifferenceMachine.start original) := rfl

def entry : Fin size := prefixLabel PrimeSimCommitPairCaller.entry

theorem start_source (raw : List Bool) :
    start raw = BitOracleInitialInput.source 7 (some entry) 0 raw := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl

theorem start_height (raw : List Bool) : TM2TapeRuns.height (start raw).stk = raw.length :=
  PrimeSimCommitPairCaller.start_height raw

#print axioms prefix_code
#print axioms difference_code
#print axioms prefix_return
#print axioms start_source
#print axioms start_height
end ExplainableCrypto.Helios.Computational.PrimeSimDifferenceCaller
