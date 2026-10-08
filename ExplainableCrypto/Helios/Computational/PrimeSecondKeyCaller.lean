import ExplainableCrypto.Helios.Computational.PrimeSecondKeyMachine
import ExplainableCrypto.Helios.Computational.PrimeSecondAllCommitCallerSource

namespace ExplainableCrypto.Helios.Computational.PrimeSecondKeyCaller
open OracleComp OracleSpec BitOracleMachine
set_option maxRecDepth 65536

def size : Nat := 7726
instance : NeZero size := ⟨by decide⟩
def prefixLayout : Fin 70 ⊕ Fin 1 ≃ Fin 71 := finSumFinEquiv
def prefixCode : Code 71 PrimeSecondAllCommitCaller.size 3 :=
  BitOracleStackFrame.code prefixLayout PrimeSecondAllCommitCaller.code
def prefixLabel (l : Fin PrimeSecondAllCommitCaller.size) : Fin size :=
  ⟨l.val,by have := l.isLt; change l.val < 7557 at this; unfold size; omega⟩
def tailLabel (l : Fin PrimeSecondKeyMachine.size) : Fin size :=
  ⟨7557+l.val,by have := l.isLt; change l.val < 169 at this; unfold size; omega⟩
def code (l : Fin size) : Command 71 size 3 :=
  if h : l.val < 7557 then
    BitOracleReturnLink.command prefixLabel (some (tailLabel 0))
      (prefixCode ⟨l.val,h⟩)
  else BitOracleReturnLink.command tailLabel none
    (PrimeSecondKeyMachine.code ⟨l.val-7557,by have := l.isLt; unfold size at this; change l.val-7557 < 169; omega⟩)
abbrev Config := BitOracleMachine.Config 71 size 3
def start (raw : List Bool) : Config :=
  BitOracleReturnLink.embed prefixLabel (some (tailLabel 0))
    (BitOracleStackFrame.embed prefixLayout (PrimeSecondAllCommitCaller.start raw) (fun _ => []))
def clock (raw : List Bool) (slack p q : Nat) :=
  PrimeSecondAllCommitCaller.clock raw slack p q+PrimeSecondKeyMachine.clock p
def cost (raw : List Bool) (slack p q : Nat) :=
  PrimeSecondAllCommitCaller.cost raw slack p q+PrimeSecondKeyMachine.cost p

theorem prefix_code (l : Fin PrimeSecondAllCommitCaller.size) : code (prefixLabel l) =
    BitOracleReturnLink.command prefixLabel (some (tailLabel 0)) (prefixCode l) := by
  have h : (prefixLabel l).val < 7557 := l.isLt
  simp only [code,dif_pos h]
  rfl

theorem tail_code (l : Fin PrimeSecondKeyMachine.size) : code (tailLabel l) =
    BitOracleReturnLink.command tailLabel none (PrimeSecondKeyMachine.code l) := by
  have h : ¬ (tailLabel l).val < 7557 := by dsimp [tailLabel]; omega
  simp only [code,dif_neg h]
  simp only [tailLabel,Nat.add_sub_cancel_left]

/-- Framing adds one blank key output. All completed p1 coordinates enter
the existing key serializer with all previous 70 words retained. -/
theorem prefix_return (original : Fin 70 → List Bool) :
    BitOracleReturnLink.embed prefixLabel (some (tailLabel 0))
      (BitOracleStackFrame.embed prefixLayout
        (⟨none,2,original⟩ : PrimeSecondAllCommitCaller.Config) (fun _ => [])) =
    BitOracleReturnLink.embed tailLabel none (PrimeSecondKeyMachine.start original) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl

def entry : Fin size := prefixLabel PrimeSecondAllCommitCaller.entry

/-- The only initialized word is the user's original encoded private input;
framing does not add prepared operands or a ready-state certificate. -/
theorem start_source (raw : List Bool) :
    start raw = BitOracleInitialInput.source 7 (some entry) 0 raw := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl

theorem start_height (raw : List Bool) : TM2TapeRuns.height (start raw).stk = raw.length := by
  rw [start_source]
  unfold TM2TapeRuns.height
  apply le_antisymm
  · apply Finset.sup_le
    intro k _
    by_cases h : k = 7
    · subst k; simp [BitOracleInitialInput.source]
    · simp [BitOracleInitialInput.source,Function.update,h]
  · have h := Finset.le_sup (f := fun k : Fin 71 =>
      ((BitOracleInitialInput.source (7 : Fin 71) (some entry) (0 : Fin 3) raw).stk k).length)
      (Finset.mem_univ (7 : Fin 71))
    simpa [BitOracleInitialInput.source] using h

#print axioms prefix_code
#print axioms tail_code
#print axioms prefix_return
#print axioms start_source
#print axioms start_height
end ExplainableCrypto.Helios.Computational.PrimeSecondKeyCaller
