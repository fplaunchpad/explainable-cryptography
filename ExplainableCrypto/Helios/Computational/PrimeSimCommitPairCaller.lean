import ExplainableCrypto.Helios.Computational.PrimeSimCommitSecondMachine

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitPairCaller
open OracleComp OracleSpec BitOracleMachine

def size : Nat := 2052
instance : NeZero size := ⟨by decide⟩
def prefixLayout : Fin 38 ⊕ Fin 1 ≃ Fin 39 := finSumFinEquiv
def prefixCode : Code 39 PrimeSimCommitCaller.size 3 :=
  BitOracleStackFrame.code prefixLayout PrimeSimCommitCaller.code
def prefixLabel (l : Fin PrimeSimCommitCaller.size) : Fin size :=
  ⟨l.val,by have := l.isLt; unfold PrimeSimCommitCaller.size at this; unfold size; omega⟩
def commitLabel (l : Fin PrimeSimCommitSecondMachine.size) : Fin size :=
  ⟨1509+l.val,by have := l.isLt; unfold PrimeSimCommitSecondMachine.size PrimeSimCommitMachine.size at this; unfold size; omega⟩
def code (l : Fin size) : Command 39 size 3 :=
  if h : l.val < 1509 then
    BitOracleReturnLink.command prefixLabel (some (commitLabel 0))
      (prefixCode ⟨l.val,h⟩)
  else BitOracleReturnLink.command commitLabel none
    (PrimeSimCommitSecondMachine.code ⟨l.val-1509,by have := l.isLt; unfold size at this; unfold PrimeSimCommitSecondMachine.size PrimeSimCommitMachine.size; omega⟩)
abbrev Config := BitOracleMachine.Config 39 size 3
def start (raw : List Bool) : Config :=
  BitOracleReturnLink.embed prefixLabel (some (commitLabel 0))
    (BitOracleStackFrame.embed prefixLayout (PrimeSimCommitCaller.start raw) (fun _ => []))
def result (answer : List Bool) (original : Fin 38 → List Bool) : Config :=
  BitOracleReturnLink.embed commitLabel none (PrimeSimCommitSecondMachine.result answer original)
def clock (raw : List Bool) (slack p q : Nat) :=
  PrimeSimCommitCaller.clock raw slack p q+PrimeSimCommitSecondMachine.clock p q
def cost (raw : List Bool) (slack p q : Nat) :=
  PrimeSimCommitCaller.cost raw slack p q+PrimeSimCommitSecondMachine.cost p q

theorem prefix_code (l : Fin PrimeSimCommitCaller.size) : code (prefixLabel l) =
    BitOracleReturnLink.command prefixLabel (some (commitLabel 0)) (prefixCode l) := by
  have h : (prefixLabel l).val < 1509 := l.isLt
  simp only [code,dif_pos h]
  rfl

theorem commit_code (l : Fin PrimeSimCommitSecondMachine.size) : code (commitLabel l) =
    BitOracleReturnLink.command commitLabel none (PrimeSimCommitSecondMachine.code l) := by
  have h : ¬ (commitLabel l).val < 1509 := by dsimp [commitLabel]; omega
  simp only [code,dif_neg h]
  simp only [commitLabel,Nat.add_sub_cancel_left]

/-- Framing adds only blank workspace. A completed prefix enters the actual
commitment program with exactly its previous 38 words and one empty private port. -/
theorem prefix_return (original : Fin 38 → List Bool) :
    BitOracleReturnLink.embed prefixLabel (some (commitLabel 0))
      (BitOracleStackFrame.embed prefixLayout
        (⟨none,2,original⟩ : PrimeSimCommitCaller.Config) (fun _ => [])) =
    BitOracleReturnLink.embed commitLabel none (PrimeSimCommitSecondMachine.start original) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl

#print axioms prefix_code
#print axioms commit_code
#print axioms prefix_return
end ExplainableCrypto.Helios.Computational.PrimeSimCommitPairCaller
