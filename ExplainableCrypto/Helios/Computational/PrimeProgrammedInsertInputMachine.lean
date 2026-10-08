import ExplainableCrypto.Helios.Computational.PrimeProgrammedStateCallerSource

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertInputMachine
open Turing.TM2 BitOracleMachine
abbrev size := 4
def copyLayout : Fin 3 ⊕ Fin 45 ≃ Fin 48 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [44, 23, 24, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 45, 46, 47] (by decide +kernel) (by decide +kernel))
def copyProgram (l : Fin 2) := TM2StackFrame.relocate copyLayout
  (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.copyPorts
    PrimeNonceCiphertextMachine.copyLabels BinaryModuloCode.memory BitCopyMachine.program l)
def copyLabel (l : Fin 2) : Fin size := ⟨2+l.val,by have := l.isLt; change _ < 4; omega⟩
def program (l : Fin size) : Stmt (fun _ : Fin 48 => Bool) (Fin size) (Fin 3) :=
  if l = 0 then .branch (fun v => v == 2)
    (.load (fun _ => 0) (.goto (fun _ => copyLabel 0))) (.load (fun _ => 1) .halt)
  else if l = 1 then .pop 44 (fun _ b => BinaryModuloCode.memory b)
    (.branch (fun v => v == 0) (.load (fun _ => 2) .halt) (.goto (fun _ => 1)))
  else TM2ReturnLink.redirect copyLabel 1
    (copyProgram ⟨l.val-2,by have := l.isLt; change l.val < 4 at this; omega⟩)
def code : Code 48 size 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 48 size 3
def tick : Config → Config := TM2ReturnLink.tick program

def start (old : Fin 48 → List Bool) : Config := ⟨some 0,2,old⟩
def resultWords (old : Fin 48 → List Bool) : Fin 48 → List Bool :=
  Function.update (Function.update old 23 (old 44)) 44 []
def result (old : Fin 48 → List Bool) : Config := ⟨none,2,resultWords old⟩
def clock (cache : List Bool) := 3*cache.length+4
def cost (cache : List Bool) := 32*clock cache

end ExplainableCrypto.Helios.Computational.PrimeProgrammedInsertInputMachine
