import ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptMachine
import ExplainableCrypto.Helios.Computational.TranscriptScalarSave

/-! Four full-field simulator draws with actual scalar saves and modulus cleanup. -/
namespace ExplainableCrypto.Helios.Computational.PrimeTranscriptDraws
open OracleComp OracleSpec BitOracleMachine

def size : Nat := 213
instance : NeZero size := ⟨by decide⟩
def sampleLabel (phase : Fin 4) (l : Fin 48) : Fin size :=
  ⟨48*phase.val+l.val,by have := phase.isLt; have := l.isLt; unfold size; omega⟩
def saveLabel (phase : Fin 3) (l : Fin 7) : Fin size :=
  ⟨192+7*phase.val+l.val,by have := phase.isLt; have := l.isLt; unfold size; omega⟩
def sampleReturn (phase : Fin 4) : Option (Fin size) :=
  if h : phase.val < 3 then some (saveLabel ⟨phase.val,h⟩ 0) else none
def saveReturn (phase : Fin 3) : Fin size := sampleLabel ⟨phase.val+1,by omega⟩ 0

def code (l : Fin size) : Command 23 size 3 :=
  if h : l.val < 192 then
    let phase : Fin 4 := ⟨l.val/48,by omega⟩
    BitOracleReturnLink.command (sampleLabel phase) (sampleReturn phase)
      (PrimeHonestTranscriptMachine.code ⟨l.val%48,by omega⟩)
  else
    let phase : Fin 3 := ⟨(l.val-192)/7,by have := l.isLt; unfold size at this; omega⟩
    BitOracleReturnLink.command (saveLabel phase) (some (saveReturn phase))
      (TranscriptScalarSave.code phase ⟨(l.val-192)%7,by omega⟩)

abbrev Config := BitOracleMachine.Config 23 size 3
def start (alpha beta nonce record first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) : Config :=
  BitOracleReturnLink.embed (sampleLabel 0) (sampleReturn 0)
    (PrimeHonestTranscriptMachine.start alpha beta nonce record first second samplerMod context modulus g pk vote (fun _ => []))
def result (c e z0 z1 scalarMod alpha beta nonce record first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) : Config :=
  BitOracleReturnLink.embed (sampleLabel 3) none
    (PrimeHonestTranscriptMachine.result z1 scalarMod alpha beta nonce record first second samplerMod context modulus g pk vote ![c,e,z0])

def scalarWidth (q : Nat) : Nat := 2*(q-1).size+1
def saveClock (q : Nat) : Nat := TranscriptScalarSave.clock (List.replicate (scalarWidth q) false) q.bits
def saveCost (q : Nat) : Nat := TranscriptScalarSave.cost (List.replicate (scalarWidth q) false) q.bits
def clock (slack q : Nat) : Nat := 4*PrimeHonestTranscriptMachine.clock slack q+3*saveClock q
def cost (slack q : Nat) : Nat := 4*PrimeHonestTranscriptMachine.cost slack q+3*saveCost q

end ExplainableCrypto.Helios.Computational.PrimeTranscriptDraws

namespace ExplainableCrypto.Helios.Computational.PrimeTranscriptDraws
open OracleComp OracleSpec BitOracleMachine

theorem sample_code (phase : Fin 4) (l : Fin 48) : code (sampleLabel phase l) =
    BitOracleReturnLink.command (sampleLabel phase) (sampleReturn phase) (PrimeHonestTranscriptMachine.code l) := by
  have h : (sampleLabel phase l).val < 192 := by have := phase.isLt; have := l.isLt; dsimp [sampleLabel]; omega
  simp only [code,dif_pos h]
  have hp : (sampleLabel phase l).val / 48 = phase.val := by have := l.isLt; dsimp [sampleLabel]; omega
  have hl : (sampleLabel phase l).val % 48 = l.val := by have := l.isLt; dsimp [sampleLabel]; omega
  simp only [hp,hl]

theorem save_code (phase : Fin 3) (l : Fin 7) : code (saveLabel phase l) =
    BitOracleReturnLink.command (saveLabel phase) (some (saveReturn phase)) (TranscriptScalarSave.code phase l) := by
  have h : ¬ (saveLabel phase l).val < 192 := by dsimp [saveLabel]; omega
  simp only [code,dif_neg h]
  have hp : ((saveLabel phase l).val-192) / 7 = phase.val := by have := l.isLt; dsimp [saveLabel]; omega
  have hl : ((saveLabel phase l).val-192) % 7 = l.val := by have := l.isLt; dsimp [saveLabel]; omega
  simp only [hp,hl]

def saveFrame (phase : Fin 3)
    (alpha beta nonce record first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) (extra : Fin 3 → List Bool) : Fin 20 → List Bool := fun k =>
  (PrimeHonestTranscriptMachine.start alpha beta nonce record first second samplerMod context modulus g pk vote extra).stk
    (TranscriptScalarSave.layout phase (.inr k))

theorem save_entry (phase : Fin 3) (word scalarMod alpha beta nonce record first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) (extra : Fin 3 → List Bool) (he : extra phase = []) :
    BitOracleReturnLink.embed (sampleLabel ⟨phase.val,by omega⟩) (sampleReturn ⟨phase.val,by omega⟩)
      (PrimeHonestTranscriptMachine.result word scalarMod alpha beta nonce record first second samplerMod context modulus g pk vote extra) =
    BitOracleReturnLink.embed (saveLabel phase) (some (saveReturn phase))
      (TranscriptScalarSave.start phase word scalarMod
        (saveFrame phase alpha beta nonce record first second samplerMod context modulus g pk vote extra)) := by
  fin_cases phase <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  all_goals
    congr 1
    funext k
    fin_cases k <;> first | rfl | exact he

theorem save_return (phase : Fin 3) (word alpha beta nonce record first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) (extra : Fin 3 → List Bool) :
    BitOracleReturnLink.embed (saveLabel phase) (some (saveReturn phase))
      (TranscriptScalarSave.result phase word
        (saveFrame phase alpha beta nonce record first second samplerMod context modulus g pk vote extra)) =
    BitOracleReturnLink.embed (sampleLabel ⟨phase.val+1,by omega⟩) (sampleReturn ⟨phase.val+1,by omega⟩)
      (PrimeHonestTranscriptMachine.start alpha beta nonce record first second samplerMod context modulus g pk vote
        (Function.update extra phase word)) := by
  fin_cases phase <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  all_goals
    congr 1
    funext k
    fin_cases k <;> rfl

#print axioms sample_code
#print axioms save_code
#print axioms save_entry
#print axioms save_return
end ExplainableCrypto.Helios.Computational.PrimeTranscriptDraws
