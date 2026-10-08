import ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextMachine
import ExplainableCrypto.Helios.Computational.PrimeTranscriptDraws

/-! Execute the retained second nonce and four fresh full-field transcript draws.
All earlier 50 words remain resident; new outputs occupy ports 50 through 58. -/
namespace ExplainableCrypto.Helios.Computational.PrimeSecondTranscriptMachine
open Turing.TM2 OracleComp OracleSpec BitOracleMachine

def size : Nat := 712
instance : NeZero size := ⟨by decide⟩
def layout : Fin 23 ⊕ Fin 36 ≃ Fin 59 :=
  finSumFinEquiv.trans (List.Nodup.getEquivOfForallMemList
    [51,23,58,24,25,26,6,57,27,28,54,55,56,52,49,15,16,50,53,19,21,20,22,0,1,2,3,4,5,7,8,9,10,11,12,13,14,17,18,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48]
    (by decide +kernel) (by decide +kernel))
def routeLabel (l : Fin 7) : Fin size := ⟨2+l.val,by unfold size; omega⟩
def encryptLabel (l : Fin 490) : Fin size := ⟨9+l.val,by unfold size; omega⟩
def drawLabel (l : Fin PrimeTranscriptDraws.size) : Fin size :=
  ⟨499+l.val,by have := l.isLt; change l.val < 213 at this; unfold size; omega⟩
def routeCode : Code 59 7 3 :=
  BitOracleStackFrame.code layout PrimeNonceCiphertextMachine.code
def encryptCode : Code 59 490 3 := BitOracleStackFrame.code layout
  (BitOracleStackFrame.code PrimeNonceCiphertextMachine.encryptLayout PrimeEncryptMachine.code)
def drawsCode : Code 59 PrimeTranscriptDraws.size 3 :=
  BitOracleStackFrame.code layout PrimeTranscriptDraws.code

def code (l : Fin size) : Command 59 size 3 :=
  if l = 0 then .compute (.branch (fun v => v == 2)
    (.push 53 (fun _ => false) (.goto (fun _ => routeLabel 0)))
    (.load (fun _ => 1) .halt))
  else if l = 1 then .compute (.branch (fun v => v == 2)
    (.load (fun _ => 0) (.goto (fun _ => encryptLabel (PrimeEncryptMachine.copyLabel 0 0))))
    (.load (fun _ => 1) .halt))
  else if h : l.val < 9 then BitOracleReturnLink.command routeLabel (some 1)
    (routeCode ⟨l.val-2,by omega⟩)
  else if h : l.val < 499 then BitOracleReturnLink.command encryptLabel
    (some (drawLabel (PrimeTranscriptDraws.sampleLabel 0 0)))
    (encryptCode ⟨l.val-9,by omega⟩)
  else BitOracleReturnLink.command drawLabel none
    (drawsCode ⟨l.val-499,by have := l.isLt; unfold size at this; change l.val-499 < 213; omega⟩)

abbrev Config := BitOracleMachine.Config 59 size 3

def start (old : Fin 50 → List Bool) : Config :=
  ⟨some 0,2,fun k => if h : k.val < 50 then old ⟨k.val,h⟩ else []⟩
def result (alpha beta nonce c e z0 z1 scalarMod : List Bool)
    (old : Fin 50 → List Bool) : Config :=
  ⟨none,2,fun k => if h : k.val < 50 then old ⟨k.val,h⟩
    else (![alpha,beta,nonce,[false],c,e,z0,z1,scalarMod] : Fin 9 → List Bool)
      ⟨k.val-50,by omega⟩⟩

/-- Canonical loaded operands plus an arbitrary retained frame. Actual source
presentation is proved separately from the preceding returned state. -/
def inputWords (record first second samplerMod context modulus g pk : List Bool)
    (frame : Fin 36 → List Bool) : Fin 50 → List Bool := fun k =>
  TM2StackFrame.data layout
    (![[],[],[],[],[],[],modulus,[],[],[],[],[],[],[],context,pk,g,[],[],record,first,second,samplerMod])
    frame ⟨k.val,by omega⟩
def frame (old : Fin 50 → List Bool) : Fin 36 → List Bool := fun k =>
  old ⟨(layout (.inr k)).val,by fin_cases k <;> decide +kernel⟩

def clock (slack p q : Nat) : Nat := 1+PrimeNonceCiphertextMachine.clock (q-1)+
  (1+PrimeEncryptMachine.clock p (q-1).size+PrimeTranscriptDraws.clock slack q)
def cost (slack p q : Nat) : Nat := 3+6*PrimeNonceCiphertextMachine.clock (q-1)+
  (3+32*PrimeEncryptMachine.clock p (q-1).size+PrimeTranscriptDraws.cost slack q)

end ExplainableCrypto.Helios.Computational.PrimeSecondTranscriptMachine
