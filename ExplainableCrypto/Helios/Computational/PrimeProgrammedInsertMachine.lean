import ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertInputMachine
import ExplainableCrypto.Helios.Computational.CacheProgrammedInsertMachine
import ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertSource

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertMachine
open OracleComp OracleSpec BitOracleMachine
abbrev size := 4+CacheProgrammedInsertMachine.size

def coreLayout : Fin 12 ⊕ Fin 36 ≃ Fin 48 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [23, 24, 25, 26, 27, 28, 46, 10, 43, 44, 45, 47, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42] (by decide +kernel) (by decide +kernel))
def coreCode : Code 48 CacheProgrammedInsertMachine.size 3 :=
  BitOracleStackFrame.code coreLayout CacheProgrammedInsertMachine.code
def prefixLabel (l : Fin 4) : Fin size :=
  ⟨l.val,by have := l.isLt; change l.val < 4+CacheProgrammedInsertMachine.size; omega⟩
def coreLabel (l : Fin CacheProgrammedInsertMachine.size) : Fin size :=
  ⟨4+l.val,by have := l.isLt; change 4+l.val < 4+CacheProgrammedInsertMachine.size; omega⟩
def code (l : Fin size) : Command 48 size 3 :=
  if h : l.val < 4 then BitOracleReturnLink.command prefixLabel (some (coreLabel 0))
    (PrimeProgrammedInsertInputMachine.code ⟨l.val,h⟩)
  else BitOracleReturnLink.command coreLabel none
    (coreCode ⟨l.val-4,by have := l.isLt; change l.val < 4+CacheProgrammedInsertMachine.size at this; omega⟩)
abbrev Config := BitOracleMachine.Config 48 size 3
def start (old : Fin 48 → List Bool) : Config :=
  BitOracleReturnLink.embed prefixLabel (some (coreLabel 0)) (PrimeProgrammedInsertInputMachine.start old)
def frame (old : Fin 48 → List Bool) : Fin 36 → List Bool := fun k => old (coreLayout (.inr k))
def insertBound (p q N : Nat) := CacheInsertMachine.cost p q N N
def inputBound (p q N : Nat) := 1+3*N+keyRecordBitBound p+groupRecordBitBound q
def prepareClock (N : Nat) := 3*N+4
def coreClock (p q N : Nat) := CacheProgrammedInsertMachine.clock (insertBound p q N) (inputBound p q N)
def clock (p q N : Nat) := prepareClock N+coreClock p q N
def cost (p q N : Nat) := 32*clock p q N

theorem prefix_code (l : Fin 4) : code (prefixLabel l) =
    BitOracleReturnLink.command prefixLabel (some (coreLabel 0)) (PrimeProgrammedInsertInputMachine.code l) := by
  have h : (prefixLabel l).val < 4 := l.isLt
  simp only [code,dif_pos h]
  rfl

theorem core_code (l : Fin CacheProgrammedInsertMachine.size) : code (coreLabel l) =
    BitOracleReturnLink.command coreLabel none (coreCode l) := by
  have h : ¬ (coreLabel l).val < 4 := by dsimp [coreLabel]; omega
  simp only [code]
  rw [dif_neg h]
  simp only [coreLabel,Nat.add_sub_cancel_left]

#print axioms prefix_code
#print axioms core_code
end ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertMachine
