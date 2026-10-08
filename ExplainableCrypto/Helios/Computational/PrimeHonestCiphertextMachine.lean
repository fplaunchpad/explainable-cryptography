import ExplainableCrypto.Helios.Computational.PrimeHonestInputMachine
import ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextCaller

/-! Execute raw constructor input initialization, then both nonce draws and
the first historical ciphertext. This is a constructor prefix, not a ballot. -/
namespace ExplainableCrypto.Helios.Computational.PrimeHonestCiphertextMachine
open Turing.TM2 OracleComp OracleSpec BitOracleMachine

def size : Nat := 753
instance : NeZero size := ⟨by decide⟩
def inputLabel (l : Fin 97) : Fin size := ⟨1+l.val,by unfold size; omega⟩
def callerLabel (l : Fin PrimeNonceCiphertextCaller.size) : Fin size :=
  ⟨98+l.val,by have := l.isLt; unfold PrimeNonceCiphertextCaller.size at this; unfold size; omega⟩
def callerEntry : Fin PrimeNonceCiphertextCaller.size :=
  PrimeNonceCiphertextCaller.pairLabel (PrimeNoncePairMachine.entryLabel 0)

def code (l : Fin size) : Command 23 size 3 :=
  if l = 0 then .compute
    (.branch (fun v => v == 2)
      (.load (fun _ => 0) (.goto (fun _ => callerLabel callerEntry)))
      (.load (fun _ => 1) .halt))
  else if h : l.val < 98 then
    BitOracleReturnLink.command inputLabel (some 0)
      (PrimeHonestInputMachine.code ⟨l.val-1,by omega⟩)
  else BitOracleReturnLink.command callerLabel none
    (PrimeNonceCiphertextCaller.code ⟨l.val-98,by
      have := l.isLt
      unfold size at this
      unfold PrimeNonceCiphertextCaller.size
      omega⟩)

abbrev Config := BitOracleMachine.Config 23 size 3
def start (raw : List Bool) : Config :=
  BitOracleReturnLink.embed inputLabel (some 0) (PrimeHonestInputMachine.start raw)
def result (alpha beta nonce record first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) : Config :=
  BitOracleReturnLink.embed callerLabel none
    (PrimeNonceCiphertextCaller.result alpha beta nonce record first second samplerMod context modulus g pk vote)
def clock (raw : List Bool) (slack p q : Nat) : Nat :=
  PrimeHonestInputMachine.clock raw + 1 + PrimeNonceCiphertextCaller.clock slack p q
def cost (raw : List Bool) (slack p q : Nat) : Nat :=
  32*PrimeHonestInputMachine.clock raw + 3 + PrimeNonceCiphertextCaller.cost slack p q

theorem input_code (l : Fin 97) : code (inputLabel l) =
    BitOracleReturnLink.command inputLabel (some 0) (PrimeHonestInputMachine.code l) := by
  have h0 : inputLabel l ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [inputLabel] at this
  have h1 : (inputLabel l).val < 98 := by dsimp [inputLabel]; omega
  simp only [code,if_neg h0,dif_pos h1]
  congr 2
  apply Fin.ext
  dsimp [inputLabel]
  omega

theorem caller_code (l : Fin PrimeNonceCiphertextCaller.size) : code (callerLabel l) =
    BitOracleReturnLink.command callerLabel none (PrimeNonceCiphertextCaller.code l) := by
  have h0 : callerLabel l ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [callerLabel] at this
  have h1 : ¬ (callerLabel l).val < 98 := by dsimp [callerLabel]; omega
  simp only [code,if_neg h0,dif_neg h1]
  congr 2
  apply Fin.ext
  dsimp [callerLabel]
  omega

theorem input_return (modulus g pk record context : List Bool) (vote : Bool) :
    step code (BitOracleReturnLink.embed inputLabel (some 0)
      (PrimeHonestInputMachine.result modulus g pk record context vote)) =
    pure (BitOracleReturnLink.embed callerLabel none
      (PrimeNonceCiphertextCaller.start g pk modulus record context vote),3) := by
  change pure (_,3) = pure (_,3)
  congr 1
  congr 1
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

#print axioms input_code
#print axioms caller_code
#print axioms input_return
end ExplainableCrypto.Helios.Computational.PrimeHonestCiphertextMachine
