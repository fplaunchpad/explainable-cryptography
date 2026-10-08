import ExplainableCrypto.Helios.Computational.PrimeNoncePairMachineSource
import ExplainableCrypto.Helios.Computational.PrimeEncryptMachine

/-! Execute the first nonce's prefix-to-digits handoff in the shared23-port
caller layout. Initial public/private input preparation remains a separate
obligation. The controller preserves every framed input literally. -/
namespace ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextMachine
open Turing.TM2

def pairLayout : Fin 11 ⊕ Fin 12 ≃ Fin 23 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [0,22,1,2,3,21,4,5,19,20,14,6,7,8,9,10,11,12,13,15,16,17,18]
    (by decide +kernel) (by decide +kernel))
def encryptLayout : Fin 19 ⊕ Fin 4 ≃ Fin 23 := finSumFinEquiv

def copyPorts : BitCopyMachine.Stack ≃ Fin 3 where
  toFun | .source => 0 | .destination => 1 | .scratch => 2
  invFun := ![.source,.destination,.scratch]
  left_inv k := by cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl
def copyLabels : Bool ≃ Fin 2 where
  toFun | false => 0 | true => 1
  invFun := ![false,true]
  left_inv k := by cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl
def copyLayout : Fin 3 ⊕ Fin 20 ≃ Fin 23 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [20,7,3,0,1,2,4,5,6,8,9,10,11,12,13,14,15,16,17,18,19,21,22]
    (by decide +kernel) (by decide +kernel))
def copyProgram (l : Fin 2) := TM2StackFrame.relocate copyLayout
  (TM2FiniteCoordinates.program copyPorts copyLabels BinaryModuloCode.memory BitCopyMachine.program l)

def parsePorts : NatPrefixMachine.Stack ≃ Fin 4 where
  toFun | .input => 0 | .count => 1 | .scratch => 2 | .output => 3
  invFun := ![.input,.count,.scratch,.output]
  left_inv k := by cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl
def parseLabels : NatPrefixMachine.Label ≃ Fin 3 where
  toFun | .width => 0 | .payload => 1 | .restore => 2
  invFun := ![.width,.payload,.restore]
  left_inv k := by cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl
def parseLayout : Fin 4 ⊕ Fin 19 ≃ Fin 23 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [7,1,2,13,0,3,4,5,6,8,9,10,11,12,14,15,16,17,18,19,20,21,22]
    (by decide +kernel) (by decide +kernel))
def parseProgram (l : Fin 3) := TM2StackFrame.relocate parseLayout
  (TM2FiniteCoordinates.program parsePorts parseLabels BinaryModuloCode.memory NatPrefixMachine.program l)

def copyLabel (l : Fin 2) : Fin 7 := ⟨2+l.val,by omega⟩
def parseLabel (l : Fin 3) : Fin 7 := ⟨4+l.val,by omega⟩

def program (l : Fin 7) : Stmt (fun _ : Fin 23 => Bool) (Fin 7) (Fin 3) :=
  if l = 0 then .branch (fun v => v == 2)
    (.load (fun _ => 0) (.goto (fun _ => copyLabel 0))) (.load (fun _ => 1) .halt)
  else if l = 1 then .branch (fun v => v == 2)
    (.peek 7 (fun _ b => BinaryModuloCode.memory b)
      (.branch (fun v => v == 0) (.load (fun _ => 2) .halt) (.load (fun _ => 1) .halt)))
    (.load (fun _ => 1) .halt)
  else if h : l.val < 4 then TM2ReturnLink.redirect copyLabel (parseLabel 0)
    (copyProgram ⟨l.val-2,by omega⟩)
  else TM2ReturnLink.redirect parseLabel 1 (parseProgram ⟨l.val-4,by omega⟩)

def code : BitOracleMachine.Code 23 7 3 := fun l => .compute (program l)
abbrev Config := BitOracleMachine.Config 23 7 3
def tick : Config → Config := TM2ReturnLink.tick program

def start (record first second samplerMod context modulus g pk : List Bool) (vote : Bool) : Config :=
  ⟨some 0,2,![[],[],[],[],[],[],modulus,[],[],[],[],[],[],[],context,pk,g,[],[vote],record,first,second,samplerMod]⟩
def result (nonce record first second samplerMod context modulus g pk : List Bool) (vote : Bool) : Config :=
  ⟨none,2,![[],[],[],[],[],[],modulus,[],[],[],[],[],[],nonce,context,pk,g,[],[vote],record,first,second,samplerMod]⟩

def pairFrame (modulus g pk : List Bool) (vote : Bool) : Fin 12 → List Bool :=
  ![modulus,[],[],[],[],[],[],[],pk,g,[],[vote]]
def clock (n : Nat) : Nat := 7*n.size+9

end ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextMachine
