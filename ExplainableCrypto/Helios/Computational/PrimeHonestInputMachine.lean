import ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextMachine
import ExplainableCrypto.Helios.Computational.CacheRequestInput
import ExplainableCrypto.Helios.Computational.BallotOutputCodec
import ExplainableCrypto.Helios.Computational.BitOracleInitialInput

/-! Fixed honest-constructor input initialization. The existing field/prefix
parsers populate the concrete23-port pair entry from one raw private record. -/
namespace ExplainableCrypto.Helios.Computational.PrimeHonestInputMachine
open Turing.TM2

def copyLayout : Fin 3 ⊕ Fin 20 ≃ Fin 23 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [7,14,3,0,1,2,4,5,6,8,9,10,11,12,13,15,16,17,18,19,20,21,22]
    (by decide +kernel) (by decide +kernel))
def copyProgram (l : Fin 2) := TM2StackFrame.relocate copyLayout
  (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.copyPorts
    PrimeNonceCiphertextMachine.copyLabels BinaryModuloCode.memory BitCopyMachine.program l)

def fieldInput (phase : Fin 7) : Fin 23 := ![7,7,9,9,7,7,7] phase
def fieldOutput (phase : Fin 7) : Fin 23 := ![8,9,8,8,19,18,8] phase

def fieldLayout (phase : Fin 7) : NatPrefixMachine.Stack ⊕ Fin 19 ≃ Fin 23 :=
  ((Equiv.sumCongr PrimeNonceCiphertextMachine.parsePorts (Equiv.refl _)).trans finSumFinEquiv).trans
    ((Equiv.swap 0 (fieldInput phase)).trans (Equiv.swap 3 (fieldOutput phase)))
def fieldProgram (phase : Fin 7) (l : Fin 9) :=
  TM2FiniteCoordinates.program (Equiv.refl (Fin 23)) CacheRequestInput.labels BinaryModuloCode.memory
    (fun k => TM2StackFrame.relocate (fieldLayout phase) (FieldPrefixMachine.program k)) l

def parseOutput (phase : Fin 3) : Fin 23 := ![6,16,15] phase
def parseLayout (phase : Fin 3) : NatPrefixMachine.Stack ⊕ Fin 19 ≃ Fin 23 :=
  ((Equiv.sumCongr PrimeNonceCiphertextMachine.parsePorts (Equiv.refl _)).trans finSumFinEquiv).trans
    ((Equiv.swap 0 8).trans (Equiv.swap 3 (parseOutput phase)))
def parseProgram (phase : Fin 3) (l : Fin 3) :=
  TM2FiniteCoordinates.program (Equiv.refl (Fin 23)) PrimeNonceCiphertextMachine.parseLabels BinaryModuloCode.memory
    (fun k => TM2StackFrame.relocate (parseLayout phase) (NatPrefixMachine.program k)) l

def copyLabel (l : Fin 2) : Fin 97 := ⟨23+l.val,by omega⟩
def fieldLabel (phase : Fin 7) (l : Fin 9) : Fin 97 := ⟨25+9*phase.val+l.val,by omega⟩
def parseLabel (phase : Fin 3) (l : Fin 3) : Fin 97 := ⟨88+3*phase.val+l.val,by omega⟩
def fieldReturn (phase : Fin 7) : Fin 97 := ![7,9,15,17,19,20,21] phase
def parseReturn (phase : Fin 3) : Fin 97 := ![8,16,18] phase

private def fail : Stmt (fun _ : Fin 23 => Bool) (Fin 97) (Fin 3) := .load (fun _ => 1) .halt
private def enter (next : Fin 97) : Stmt (fun _ : Fin 23 => Bool) (Fin 97) (Fin 3) :=
  .load (fun _ => 0) (.goto (fun _ => next))
private def guard (next : Stmt (fun _ : Fin 23 => Bool) (Fin 97) (Fin 3)) :=
  Stmt.branch (fun v => v == 2) next fail
private def empty (port : Fin 23) (next : Stmt (fun _ : Fin 23 => Bool) (Fin 97) (Fin 3)) :=
  Stmt.peek port (fun _ b => BinaryModuloCode.memory b)
    (.branch (fun v => v == 0) next fail)
private def expect (port : Fin 23) (bit : Bool) (next : Fin 97) :
    Stmt (fun _ : Fin 23 => Bool) (Fin 97) (Fin 3) :=
  .pop port (fun _ b => BinaryModuloCode.memory b)
    (.branch (fun v => v == (if bit then 2 else 1)) (enter next) fail)
private def voteTail (bit : Bool) : Stmt (fun _ : Fin 23 => Bool) (Fin 97) (Fin 3) :=
  empty 18 (.push 18 (fun _ => bit) (enter (fieldLabel 6 0)))
private def voteCheck : Stmt (fun _ : Fin 23 => Bool) (Fin 97) (Fin 3) :=
  .pop 18 (fun _ b => BinaryModuloCode.memory b)
    (.branch (fun v => v == 2) (voteTail true)
      (.branch (fun v => v == 1) (voteTail false) fail))

/-- Literal count checks consume the existing U5 and U2 encodings. -/
def control (l : Fin 23) : Stmt (fun _ : Fin 23 => Bool) (Fin 97) (Fin 3) :=
  if h : l.val < 7 then
    expect 7 (![true,true,true,false,true,false,true] ⟨l.val,h⟩)
      (if l.val = 6 then fieldLabel 0 0 else ⟨l.val+1,by omega⟩)
  else if l = 7 then guard (enter (parseLabel 0 0))
  else if l = 8 then guard (empty 8 (enter (fieldLabel 1 0)))
  else if l = 9 then guard (enter 10)
  else if h : l.val < 15 then
    expect 9 (![true,true,false,false,true] ⟨l.val-10,by omega⟩)
      (if l.val = 14 then fieldLabel 2 0 else ⟨l.val+1,by omega⟩)
  else if l = 15 then guard (enter (parseLabel 1 0))
  else if l = 16 then guard (empty 8 (enter (fieldLabel 3 0)))
  else if l = 17 then guard (enter (parseLabel 2 0))
  else if l = 18 then guard (empty 8 (empty 9 (enter (fieldLabel 4 0))))
  else if l = 19 then guard (enter (fieldLabel 5 0))
  else if l = 20 then guard voteCheck
  else if l = 21 then guard (empty 7 (enter 22))
  else .pop 8 (fun _ b => BinaryModuloCode.memory b)
    (.branch (fun v => v == 0) (.load (fun _ => 2) .halt) (.goto (fun _ => 22)))

def program (l : Fin 97) : Stmt (fun _ : Fin 23 => Bool) (Fin 97) (Fin 3) :=
  if h : l.val < 23 then control ⟨l.val,h⟩
  else if h : l.val < 25 then
    TM2ReturnLink.redirect copyLabel 0 (copyProgram ⟨l.val-23,by omega⟩)
  else if h : l.val < 88 then
    let phase : Fin 7 := ⟨(l.val-25)/9,by omega⟩
    TM2ReturnLink.redirect (fieldLabel phase) (fieldReturn phase)
      (fieldProgram phase ⟨(l.val-25)%9,Nat.mod_lt _ (by decide)⟩)
  else
    let phase : Fin 3 := ⟨(l.val-88)/3,by omega⟩
    TM2ReturnLink.redirect (parseLabel phase) (parseReturn phase)
      (parseProgram phase ⟨(l.val-88)%3,Nat.mod_lt _ (by decide)⟩)

def code : BitOracleMachine.Code 23 97 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 23 97 3
def tick : Config → Config := TM2ReturnLink.tick program

def input {p q : Nat} [NeZero p] [NeZero q] (g pk : PrimeGroup p q)
    (slack : Nat) (vote : Bool) (saved : List Bool) : List Bool :=
  bitFieldsEncode [uniformNatEncode p,(ballotCiphertextBitCodec p q).encode (g,pk),
    SamplerOperands.input slack q [],[vote],saved]

def start (raw : List Bool) : Config := BitOracleInitialInput.source 7 (some (copyLabel 0)) 0 raw
/-- Halted complete pair-entry data; the enclosing caller must check/reset memory. -/
def result (modulus g pk record context : List Bool) (vote : Bool) : Config :=
  ⟨none,2,![[],[],[],[],[],[],modulus,[],[],[],[],[],[],[],context,pk,g,[],[vote],record,[],[],[]]⟩

def clock (raw : List Bool) : Nat := 14*raw.length*raw.length+54*raw.length+83

end ExplainableCrypto.Helios.Computational.PrimeHonestInputMachine
