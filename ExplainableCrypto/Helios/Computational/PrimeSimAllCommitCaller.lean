import ExplainableCrypto.Helios.Computational.PrimeSimOneTail
import ExplainableCrypto.Helios.Computational.PrimeSimDifferenceCallerSource

namespace ExplainableCrypto.Helios.Computational.PrimeSimAllCommitCaller
open OracleComp OracleSpec BitOracleMachine

def size : Nat := 3484
instance : NeZero size := ⟨by decide⟩
def prefixLayout : Fin 39 ⊕ Fin 4 ≃ Fin 43 := finSumFinEquiv
def prefixCode : Code 43 PrimeSimDifferenceCaller.size 3 :=
  BitOracleStackFrame.code prefixLayout PrimeSimDifferenceCaller.code
def prefixLabel (l : Fin PrimeSimDifferenceCaller.size) : Fin size :=
  ⟨l.val,by have := l.isLt; unfold PrimeSimDifferenceCaller.size at this; unfold size; omega⟩
def tailLabel (l : Fin PrimeSimOneTail.size) : Fin size :=
  ⟨2118+l.val,by have := l.isLt; unfold PrimeSimOneTail.size at this; unfold size; omega⟩
def code (l : Fin size) : Command 43 size 3 :=
  if h : l.val < 2118 then
    BitOracleReturnLink.command prefixLabel (some (tailLabel 0))
      (prefixCode ⟨l.val,h⟩)
  else BitOracleReturnLink.command tailLabel none
    (PrimeSimOneTail.code ⟨l.val-2118,by have := l.isLt; unfold size at this; unfold PrimeSimOneTail.size; omega⟩)
abbrev Config := BitOracleMachine.Config 43 size 3
def start (raw : List Bool) : Config :=
  BitOracleReturnLink.embed prefixLabel (some (tailLabel 0))
    (BitOracleStackFrame.embed prefixLayout (PrimeSimDifferenceCaller.start raw) (fun _ => []))
def clock (raw : List Bool) (slack p q : Nat) :=
  PrimeSimDifferenceCaller.clock raw slack p q+PrimeSimOneTail.clock p q
def cost (raw : List Bool) (slack p q : Nat) :=
  PrimeSimDifferenceCaller.cost raw slack p q+PrimeSimOneTail.cost p q

theorem prefix_code (l : Fin PrimeSimDifferenceCaller.size) : code (prefixLabel l) =
    BitOracleReturnLink.command prefixLabel (some (tailLabel 0)) (prefixCode l) := by
  have h : (prefixLabel l).val < 2118 := l.isLt
  simp only [code,dif_pos h]
  rfl

theorem tail_code (l : Fin PrimeSimOneTail.size) : code (tailLabel l) =
    BitOracleReturnLink.command tailLabel none (PrimeSimOneTail.code l) := by
  have h : ¬ (tailLabel l).val < 2118 := by dsimp [tailLabel]; omega
  simp only [code,dif_neg h]
  simp only [tailLabel,Nat.add_sub_cancel_left]

/-- Framing adds only blank workspace. A completed prefix enters the actual
one-branch tail with exactly its previous 39 words and four empty private ports. -/
theorem prefix_return (original : Fin 39 → List Bool) :
    BitOracleReturnLink.embed prefixLabel (some (tailLabel 0))
      (BitOracleStackFrame.embed prefixLayout
        (⟨none,2,original⟩ : PrimeSimDifferenceCaller.Config) (fun _ => [])) =
    BitOracleReturnLink.embed tailLabel none (PrimeSimOneTail.start original) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl

def entry : Fin size := prefixLabel PrimeSimDifferenceCaller.entry

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
  · have h := Finset.le_sup (f := fun k : Fin 43 =>
      ((BitOracleInitialInput.source (7 : Fin 43) (some entry) (0 : Fin 3) raw).stk k).length)
      (Finset.mem_univ (7 : Fin 43))
    simpa [BitOracleInitialInput.source] using h

/-- Relabelling the completed raw difference caller retains its entire state. -/
theorem difference_source_words {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    (PrimeSimDifferenceCaller.sourceResult slack g pk vote saved out).stk =
      (PrimeSimDifferenceMachine.sourceResult slack g pk vote saved out).stk := rfl

#print axioms difference_source_words
#print axioms prefix_code
#print axioms tail_code
#print axioms prefix_return
#print axioms start_source
#print axioms start_height
end ExplainableCrypto.Helios.Computational.PrimeSimAllCommitCaller
