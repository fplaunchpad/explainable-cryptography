import ExplainableCrypto.Helios.Computational.PrimeRemainingProofRequests

/-! One concrete raw caller uses the same complete request code twice, with
executed reentry between requests. No source-ready state is supplied at entry. -/
namespace ExplainableCrypto.Helios.Computational.PrimeRemainingProofCaller
open OracleComp OracleSpec BitOracleMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
abbrev prefixSize := 4327
abbrev reentrySize := 119
abbrev requestSize := 5153
def size := 14871
instance : NeZero size := ⟨by decide⟩
abbrev Config := BitOracleMachine.Config 58 size 3

def prefixLayout : Fin 50 ⊕ Fin 8 ≃ Fin 58 := finSumFinEquiv
def prefixCode := BitOracleStackFrame.code prefixLayout PrimeProgramOutputCaller.code
def p1Code := BitOracleStackFrame.code PrimeRemainingProofRequests.p1Layout PrimeProofRequest.code
def totalCode := BitOracleStackFrame.code PrimeRemainingProofRequests.totalLayout PrimeProofRequest.code
def requestEntry : Fin requestSize := PrimeProofRequest.drawLabel PrimeRequestDraws.entry

def prefixLabel (l : Fin prefixSize) : Fin size := ⟨l.val,by have h := l.isLt; change l.val < 4327 at h; change l.val < 14871; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega⟩

def prepareP1Label (l : Fin reentrySize) : Fin size := ⟨4327+l.val,by have h := l.isLt; change l.val < 119 at h; change 4327+l.val < 14871; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega⟩

def p1Label (l : Fin requestSize) : Fin size := ⟨4446+l.val,by have h := l.isLt; change l.val < 5153 at h; change 4446+l.val < 14871; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega⟩

def prepareTotalLabel (l : Fin reentrySize) : Fin size := ⟨9599+l.val,by have h := l.isLt; change l.val < 119 at h; change 9599+l.val < 14871; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega⟩

def totalLabel (l : Fin requestSize) : Fin size := ⟨9718+l.val,by have h := l.isLt; change l.val < 5153 at h; change 9718+l.val < 14871; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega⟩


def code (l : Fin size) : Command 58 size 3 :=
  if h0 : l.val < 4327 then
    BitOracleReturnLink.command prefixLabel (some (prepareP1Label 0)) (prefixCode ⟨l.val,by change l.val < prefixSize; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega⟩)
  else if h1 : l.val < 4446 then
    BitOracleReturnLink.command prepareP1Label (some (p1Label requestEntry)) (PrimeProofRequestReentry.code ⟨l.val-(4327),by change l.val-(4327) < reentrySize; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega⟩)
  else if h2 : l.val < 9599 then
    BitOracleReturnLink.command p1Label (some (prepareTotalLabel 1)) (p1Code ⟨l.val-(4446),by change l.val-(4446) < requestSize; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega⟩)
  else if h3 : l.val < 9718 then
    BitOracleReturnLink.command prepareTotalLabel (some (totalLabel requestEntry)) (PrimeProofRequestReentry.code ⟨l.val-(9599),by change l.val-(9599) < reentrySize; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega⟩)
  else
    BitOracleReturnLink.command totalLabel (none) (totalCode ⟨l.val-(9718),by have := l.isLt; change l.val < 14871 at this; change l.val-(9718) < requestSize; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega⟩)

theorem prefix_code (l : Fin prefixSize) : code (prefixLabel l) =
    BitOracleReturnLink.command prefixLabel (some (prepareP1Label 0)) (prefixCode l) := by
  have h0 : (prefixLabel l).val < 4327 := by have := l.isLt; dsimp [prefixLabel]; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega
  simp only [code]
  rw [dif_pos h0]
  rfl

theorem prepareP1_code (l : Fin reentrySize) : code (prepareP1Label l) =
    BitOracleReturnLink.command prepareP1Label (some (p1Label requestEntry)) (PrimeProofRequestReentry.code l) := by
  have h0 : ¬ (prepareP1Label l).val < 4327 := by have := l.isLt; dsimp [prepareP1Label]; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega
  have h1 : (prepareP1Label l).val < 4446 := by have := l.isLt; dsimp [prepareP1Label]; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega
  simp only [code]
  rw [dif_neg h0,dif_pos h1]
  simp only [prepareP1Label,Nat.add_sub_cancel_left]

theorem p1_code (l : Fin requestSize) : code (p1Label l) =
    BitOracleReturnLink.command p1Label (some (prepareTotalLabel 1)) (p1Code l) := by
  have h0 : ¬ (p1Label l).val < 4327 := by have := l.isLt; dsimp [p1Label]; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega
  have h1 : ¬ (p1Label l).val < 4446 := by have := l.isLt; dsimp [p1Label]; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega
  have h2 : (p1Label l).val < 9599 := by have := l.isLt; dsimp [p1Label]; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega
  simp only [code]
  rw [dif_neg h0,dif_neg h1,dif_pos h2]
  simp only [p1Label,Nat.add_sub_cancel_left]
  rfl

theorem prepareTotal_code (l : Fin reentrySize) : code (prepareTotalLabel l) =
    BitOracleReturnLink.command prepareTotalLabel (some (totalLabel requestEntry)) (PrimeProofRequestReentry.code l) := by
  have h0 : ¬ (prepareTotalLabel l).val < 4327 := by have := l.isLt; dsimp [prepareTotalLabel]; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega
  have h1 : ¬ (prepareTotalLabel l).val < 4446 := by have := l.isLt; dsimp [prepareTotalLabel]; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega
  have h2 : ¬ (prepareTotalLabel l).val < 9599 := by have := l.isLt; dsimp [prepareTotalLabel]; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega
  have h3 : (prepareTotalLabel l).val < 9718 := by have := l.isLt; dsimp [prepareTotalLabel]; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega
  simp only [code]
  rw [dif_neg h0,dif_neg h1,dif_neg h2,dif_pos h3]
  simp only [prepareTotalLabel,Nat.add_sub_cancel_left]

theorem total_code (l : Fin requestSize) : code (totalLabel l) =
    BitOracleReturnLink.command totalLabel (none) (totalCode l) := by
  have h0 : ¬ (totalLabel l).val < 4327 := by have := l.isLt; dsimp [totalLabel]; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega
  have h1 : ¬ (totalLabel l).val < 4446 := by have := l.isLt; dsimp [totalLabel]; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega
  have h2 : ¬ (totalLabel l).val < 9599 := by have := l.isLt; dsimp [totalLabel]; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega
  have h3 : ¬ (totalLabel l).val < 9718 := by have := l.isLt; dsimp [totalLabel]; dsimp only [prefixSize,reentrySize,requestSize,size] at *; omega
  simp only [code]
  rw [dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3]
  simp only [totalLabel,Nat.add_sub_cancel_left]
  rfl

def entry : Fin size := prefixLabel PrimeProgramOutputCaller.entry
def start (raw : List Bool) : Config :=
  BitOracleReturnLink.embed prefixLabel (some (prepareP1Label 0))
    (BitOracleStackFrame.embed prefixLayout (PrimeProgramOutputCaller.start raw) (fun _ => []))

def initialWords (old : Fin 50 → List Bool) : Fin 58 → List Bool :=
  TM2StackFrame.data prefixLayout old (fun _ => [])

theorem prefix_return (old : Fin 50 → List Bool) :
    BitOracleReturnLink.embed prefixLabel (some (prepareP1Label 0))
      (BitOracleStackFrame.embed prefixLayout
        (⟨none,2,old⟩ : PrimeProgramOutputCaller.Config) (fun _ => [])) =
    BitOracleReturnLink.embed prepareP1Label (some (p1Label requestEntry))
      (PrimeProofRequestReentry.start false (initialWords old)) := by rfl

theorem p1_return (old : Fin 58 → List Bool) :
    BitOracleReturnLink.embed p1Label (some (prepareTotalLabel 1))
      (⟨none,2,old⟩ : BitOracleMachine.Config 58 requestSize 3) =
    BitOracleReturnLink.embed prepareTotalLabel (some (totalLabel requestEntry))
      (PrimeProofRequestReentry.start true old) := by rfl

theorem start_source (raw : List Bool) :
    start raw = BitOracleInitialInput.source 7 (some entry) 0 raw := by
  rw [start,PrimeProgramOutputCaller.start_source]
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

theorem start_height (raw : List Bool) : TM2TapeRuns.height (start raw).stk = raw.length := by
  rw [start_source]
  unfold TM2TapeRuns.height
  apply le_antisymm
  · apply Finset.sup_le
    intro k _
    by_cases h : k = 7
    · subst k; simp [BitOracleInitialInput.source]
    · simp [BitOracleInitialInput.source,Function.update,h]
  · have h := Finset.le_sup (f := fun k : Fin 58 =>
      ((BitOracleInitialInput.source (7 : Fin 58) (some entry) (0 : Fin 3) raw).stk k).length)
      (Finset.mem_univ (7 : Fin 58))
    simpa [BitOracleInitialInput.source] using h

#print axioms prefix_code
#print axioms prepareP1_code
#print axioms p1_code
#print axioms prepareTotal_code
#print axioms total_code
#print axioms prefix_return
#print axioms p1_return
#print axioms start_source
#print axioms start_height
end ExplainableCrypto.Helios.Computational.PrimeRemainingProofCaller
