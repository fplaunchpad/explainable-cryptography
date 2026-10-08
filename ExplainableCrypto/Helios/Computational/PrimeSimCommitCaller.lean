import ExplainableCrypto.Helios.Computational.PrimeSimCommitMachineSpec

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitCaller
open OracleComp OracleSpec BitOracleMachine

def size : Nat := 1509
instance : NeZero size := ⟨by decide⟩
def prefixLayout : Fin 23 ⊕ Fin 15 ≃ Fin 38 := finSumFinEquiv
def prefixCode : Code 38 PrimeHonestTranscriptCaller.size 3 :=
  BitOracleStackFrame.code prefixLayout PrimeHonestTranscriptCaller.code
def prefixLabel (l : Fin PrimeHonestTranscriptCaller.size) : Fin size :=
  ⟨l.val,by have := l.isLt; unfold PrimeHonestTranscriptCaller.size at this; unfold size; omega⟩
def commitLabel (l : Fin PrimeSimCommitMachine.size) : Fin size :=
  ⟨966+l.val,by have := l.isLt; unfold PrimeSimCommitMachine.size at this; unfold size; omega⟩
def code (l : Fin size) : Command 38 size 3 :=
  if h : l.val < 966 then
    BitOracleReturnLink.command prefixLabel (some (commitLabel 0))
      (prefixCode ⟨l.val,h⟩)
  else BitOracleReturnLink.command commitLabel none
    (PrimeSimCommitMachine.code ⟨l.val-966,by have := l.isLt; unfold size at this; unfold PrimeSimCommitMachine.size; omega⟩)
abbrev Config := BitOracleMachine.Config 38 size 3
def start (raw : List Bool) : Config :=
  BitOracleReturnLink.embed prefixLabel (some (commitLabel 0))
    (BitOracleStackFrame.embed prefixLayout (PrimeHonestTranscriptCaller.start raw) (fun _ => []))
def result (answer : List Bool) (original : Fin 23 → List Bool) : Config :=
  BitOracleReturnLink.embed commitLabel none (PrimeSimCommitMachine.result answer original)
def clock (raw : List Bool) (slack p q : Nat) :=
  PrimeHonestTranscriptCaller.clock raw slack p q+PrimeSimCommitMachine.clock p q
def cost (raw : List Bool) (slack p q : Nat) :=
  PrimeHonestTranscriptCaller.cost raw slack p q+PrimeSimCommitMachine.cost p q

theorem prefix_code (l : Fin PrimeHonestTranscriptCaller.size) : code (prefixLabel l) =
    BitOracleReturnLink.command prefixLabel (some (commitLabel 0)) (prefixCode l) := by
  have h : (prefixLabel l).val < 966 := l.isLt
  simp only [code,dif_pos h]
  rfl

theorem commit_code (l : Fin PrimeSimCommitMachine.size) : code (commitLabel l) =
    BitOracleReturnLink.command commitLabel none (PrimeSimCommitMachine.code l) := by
  have h : ¬ (commitLabel l).val < 966 := by dsimp [commitLabel]; omega
  simp only [code,dif_neg h]
  simp only [commitLabel,Nat.add_sub_cancel_left]

/-- Framing adds only blank workspace. A completed prefix enters the actual
commitment program with exactly its previous23words and15empty private ports. -/
theorem prefix_return (original : Fin 23 → List Bool) :
    BitOracleReturnLink.embed prefixLabel (some (commitLabel 0))
      (BitOracleStackFrame.embed prefixLayout
        (⟨none,2,original⟩ : PrimeHonestTranscriptCaller.Config) (fun _ => [])) =
    BitOracleReturnLink.embed commitLabel none (PrimeSimCommitMachine.start original) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl

#print axioms prefix_code
#print axioms commit_code
#print axioms prefix_return
end ExplainableCrypto.Helios.Computational.PrimeSimCommitCaller
