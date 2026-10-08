import ExplainableCrypto.Helios.Computational.PrimeTranscriptDraws
import ExplainableCrypto.Helios.Computational.PrimeHonestCiphertextMachine

/-! Original raw input through the first ciphertext and four simulator draws. -/
namespace ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCaller
open OracleComp OracleSpec BitOracleMachine

def size : Nat := 966
instance : NeZero size := ⟨by decide⟩
def cipherLabel (l : Fin PrimeHonestCiphertextMachine.size) : Fin size :=
  ⟨l.val,by have := l.isLt; unfold PrimeHonestCiphertextMachine.size at this; unfold size; omega⟩
def drawLabel (l : Fin PrimeTranscriptDraws.size) : Fin size :=
  ⟨753+l.val,by have := l.isLt; unfold PrimeTranscriptDraws.size at this; unfold size; omega⟩
def code (l : Fin size) : Command 23 size 3 :=
  if h : l.val < 753 then
    BitOracleReturnLink.command cipherLabel (some (drawLabel (PrimeTranscriptDraws.sampleLabel 0 0)))
      (PrimeHonestCiphertextMachine.code ⟨l.val,h⟩)
  else BitOracleReturnLink.command drawLabel none
    (PrimeTranscriptDraws.code ⟨l.val-753,by have := l.isLt; unfold size at this; unfold PrimeTranscriptDraws.size; omega⟩)

abbrev Config := BitOracleMachine.Config 23 size 3
def start (raw : List Bool) : Config :=
  BitOracleReturnLink.embed cipherLabel (some (drawLabel (PrimeTranscriptDraws.sampleLabel 0 0)))
    (PrimeHonestCiphertextMachine.start raw)
def result (c e z0 z1 scalarMod alpha beta nonce record first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) : Config :=
  BitOracleReturnLink.embed drawLabel none
    (PrimeTranscriptDraws.result c e z0 z1 scalarMod alpha beta nonce record first second samplerMod context modulus g pk vote)
def clock (raw : List Bool) (slack p q : Nat) :=
  PrimeHonestCiphertextMachine.clock raw slack p q + PrimeTranscriptDraws.clock slack q
def cost (raw : List Bool) (slack p q : Nat) :=
  PrimeHonestCiphertextMachine.cost raw slack p q + PrimeTranscriptDraws.cost slack q

theorem cipher_code (l : Fin PrimeHonestCiphertextMachine.size) : code (cipherLabel l) =
    BitOracleReturnLink.command cipherLabel (some (drawLabel (PrimeTranscriptDraws.sampleLabel 0 0)))
      (PrimeHonestCiphertextMachine.code l) := by
  have h : (cipherLabel l).val < 753 := l.isLt
  simp only [code,dif_pos h]
  rfl

theorem draw_code (l : Fin PrimeTranscriptDraws.size) : code (drawLabel l) =
    BitOracleReturnLink.command drawLabel none (PrimeTranscriptDraws.code l) := by
  have h : ¬ (drawLabel l).val < 753 := by dsimp [drawLabel]; omega
  simp only [code,dif_neg h]
  simp only [drawLabel,Nat.add_sub_cancel_left]

theorem cipher_return (alpha beta nonce record first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) :
    BitOracleReturnLink.embed cipherLabel (some (drawLabel (PrimeTranscriptDraws.sampleLabel 0 0)))
      (PrimeHonestCiphertextMachine.result alpha beta nonce record first second samplerMod context modulus g pk vote) =
    BitOracleReturnLink.embed drawLabel none
      (PrimeTranscriptDraws.start alpha beta nonce record first second samplerMod context modulus g pk vote) := by
  rfl

#print axioms cipher_code
#print axioms draw_code
#print axioms cipher_return
end ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCaller
