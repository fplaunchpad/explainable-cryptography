import ExplainableCrypto.Helios.Computational.CacheHashDispatch

/-! Executed storage transitions between the two nonzero nonce draws. -/
namespace ExplainableCrypto.Helios.Computational.PrimeNoncePairTransport
open Turing.TM2 BitOracleMachine

def size : Nat := 7
instance : NeZero size := ⟨by decide⟩
def betweenEntry : Fin size := 3

private def copyPorts : BitCopyMachine.Stack ≃ Fin 3 where
  toFun | .source => 0 | .destination => 1 | .scratch => 2
  invFun k := if k = 0 then .source else if k = 1 then .destination else .scratch
  left_inv k := by cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl
private def copyLabels : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun k := k == 1
  left_inv b := by cases b <;> rfl
  right_inv k := by fin_cases k <;> rfl
private def copyTable (which : Fin 2) : List (Fin 11) :=
  ![[8,4,0,1,2,3,5,6,7,9,10],[5,9,0,1,2,3,4,6,7,8,10]] which
def copyLayout (which : Fin 2) : BitCopyMachine.Stack ⊕ Fin 8 ≃ Fin 11 :=
  ((Equiv.sumCongr copyPorts (Equiv.refl _)).trans finSumFinEquiv).trans
    ((finCongr (show 11 = (copyTable which).length by fin_cases which <;> rfl)).trans
      (List.Nodup.getEquivOfForallMemList (copyTable which)
        (by fin_cases which <;> decide +kernel) (by fin_cases which <;> decide +kernel)))
def copyCode (which : Fin 2) :=
  TM2FiniteCoordinates.program (Equiv.refl (Fin 11)) copyLabels BinaryModuloCode.memory
    (fun label => TM2StackFrame.relocate (copyLayout which) (BitCopyMachine.program label))
def copyLabel (which : Fin 2) (label : Fin 2) : Fin size :=
  ⟨3*which.val+label.val,by have := which.isLt; have := label.isLt; unfold size; omega⟩
def copyReturn (which : Fin 2) : Fin size := if which = 0 then 2 else 5
def enter (next : Fin size) : Stmt (fun _ : Fin 11 => Bool) (Fin size) (Fin 3) :=
  .load (fun _ => 0) (.goto (fun _ => next))
def clear (port : Fin 11) (again next : Fin size) :
    Stmt (fun _ : Fin 11 => Bool) (Fin size) (Fin 3) :=
  .pop port (fun _ b => CoinWordLoader.encode b)
    (.branch (fun v => v == 0) (enter next) (.goto (fun _ => again)))
def code (label : Fin size) : Command 11 size 3 :=
  ![BitOracleReturnLink.command (copyLabel 0) (some 2) (.compute (copyCode 0 0)),
    BitOracleReturnLink.command (copyLabel 0) (some 2) (.compute (copyCode 0 1)),
    .compute (.load (fun _ => 0) .halt),
    BitOracleReturnLink.command (copyLabel 1) (some 5) (.compute (copyCode 1 0)),
    BitOracleReturnLink.command (copyLabel 1) (some 5) (.compute (copyCode 1 1)),
    .compute (clear 5 5 6), .compute (clear 1 6 0)] label

def entryStart (record savedNonce context : List Bool) : Config 11 size 3 :=
  ⟨some 0,0,![[],[],[],[],[],[],[],[],record,savedNonce,context]⟩
def betweenStart (record modulus nonce context : List Bool) : Config 11 size 3 :=
  ⟨some betweenEntry,2,![[],modulus,[],[],[],nonce,[],[],record,[],context]⟩
def ready (record savedNonce context : List Bool) : Config 11 size 3 :=
  ⟨none,0,![[],[],[],[],record,[],[],[],record,savedNonce,context]⟩
def entryClock (record : List Bool) : Nat := 2*record.length+3
def entryCost (record : List Bool) : Nat := 9*(record.length+1)+2
def betweenClock (record modulus nonce : List Bool) : Nat :=
  (2*nonce.length+2)+(nonce.length+1)+(modulus.length+1)+entryClock record
def betweenCost (record modulus nonce : List Bool) : Nat :=
  9*(nonce.length+1)+4*(nonce.length+1)+4*(modulus.length+1)+entryCost record

end ExplainableCrypto.Helios.Computational.PrimeNoncePairTransport
