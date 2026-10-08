import ExplainableCrypto.Helios.Computational.NatFieldWriterMachine

namespace ExplainableCrypto.Helios.Computational.PrimeSimKeyMachine
open Turing.TM2 BitOracleMachine
abbrev size := 169

/-- Reverse of the actual flat ballot-key record order. -/
def sourcePort : Fin 8 → Fin 43 := ![42,40,38,3,0,17,15,16]
def baseLayout : Fin 7 ⊕ Fin 37 ≃ Fin 44 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [42,43,23,24,25,26,27,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,28,29,30,31,32,33,34,35,36,37,38,39,40,41]
    (by decide +kernel) (by decide +kernel))
def layout (which : Fin 8) : Fin 7 ⊕ Fin 37 ≃ Fin 44 :=
  baseLayout.trans (Equiv.swap 42 (sourcePort which).castSucc)
def fieldProgram (which : Fin 8) (l : Fin 21) :=
  TM2StackFrame.relocate (layout which) (NatFieldWriterMachine.program l)
def fieldLabel (which : Fin 8) (l : Fin 21) : Fin 169 :=
  ⟨21*which.val+l.val,by have := which.isLt; have := l.isLt; omega⟩
def next (which : Fin 8) : Fin 169 := ⟨21*(which.val+1),by have := which.isLt; omega⟩
/-- This is U(8), pushed from its final bit toward its first bit. -/
def countPrefix : List Bool := [true,true,true,true,false,false,false,false,true]
def finish : Stmt (fun _ : Fin 44 => Bool) (Fin 169) (Fin 3) :=
  .branch (fun v => v == 2)
    (countPrefix.foldl (fun s b => .push 43 (fun _ => b) s) (.load (fun _ => 2) .halt))
    (.load (fun _ => 1) .halt)
def program (l : Fin 169) : Stmt (fun _ : Fin 44 => Bool) (Fin 169) (Fin 3) :=
  if h : l.val < 168 then
    TM2ReturnLink.redirect (fieldLabel ⟨l.val/21,by omega⟩) (next ⟨l.val/21,by omega⟩)
      (fieldProgram ⟨l.val/21,by omega⟩ ⟨l.val%21,by omega⟩)
  else finish
def code : Code 44 169 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 44 169 3
def tick : Config → Config := TM2ReturnLink.tick program

def initialWords (old : Fin 43 → List Bool) : Fin 44 → List Bool :=
  fun k => if h : k.val < 43 then old ⟨k.val,h⟩ else []
def start (old : Fin 43 → List Bool) : Config := ⟨some 0,2,initialWords old⟩
def result (key : List Bool) (old : Fin 43 → List Bool) : Config :=
  ⟨none,2,Function.update (initialWords old) 43 key⟩
def clock (p : Nat) := 8*NatFieldWriterMachine.clock (p-1)+1
def cost (p : Nat) := 32*clock p

end ExplainableCrypto.Helios.Computational.PrimeSimKeyMachine
