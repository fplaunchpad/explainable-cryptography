import ExplainableCrypto.Helios.Computational.NativeQueryExportAdapter
import ExplainableCrypto.Helios.Computational.NativeQueryReadWord
import ExplainableCrypto.Helios.Computational.BitOracleStackFrame

/-! The actual exporter framed with the original before cells and arbitrary
independent private words. The complete original storage survives execution. -/
namespace ExplainableCrypto.Helios.Computational.NativeQueryExportFrame
open Turing OracleComp OracleSpec
open BitTapeCoverage (Cell cells cellCode)
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

abbrev Config (n : Nat) := BitOracleMachine.Config (3+(n+1)) 4 3

def layout (n : Nat) : Fin 3 ⊕ Fin (n+1) ≃ Fin (3+(n+1)) := finSumFinEquiv

def frame {n : Nat} (before : List Cell) (privateWords : Fin n → List Bool) :
    Fin (n+1) → List Bool := Fin.cases (cells before) privateWords

def code (n : Nat) := BitOracleStackFrame.code (layout n) NativeQueryExportAdapter.code

def initial {n : Nat} (head : Cell) (before after : List Cell)
    (privateWords : Fin n → List Bool) : Config n :=
  BitOracleStackFrame.embed (layout n) (NativeQueryExportAdapter.initial head after)
    (frame before privateWords)

def result {n : Nat} (head : Cell) (before after : List Cell)
    (privateWords : Fin n → List Bool) : Config n :=
  BitOracleStackFrame.embed (layout n) (NativeQueryExportAdapter.result head after)
    (frame before privateWords)

/-- Successful output is exactly the existing native query decoder, for every
finite representation, including interior or trailing blank cells. -/
theorem native_result {n l : Nat} (label : Option (Fin l)) (head : Cell)
    (before after : List Cell) (privateWords : Fin n → List Bool) :
    (result head before after privateWords).stk (layout n (.inl 1)) =
      OracleTapeDispatch.readWord (BitTapeCoverage.tape ⟨label,head,before,after⟩) := by
  change NativeQueryExport.wordPrefix (head::after) = _
  exact NativeQueryReadWord.readWord label head before after

/-- Native head and both complete encoded halves are retained byte for byte. -/
theorem native_storage {n : Nat} (head : Cell) (before after : List Cell)
    (privateWords : Fin n → List Bool) :
    (result head before after privateWords).var = cellCode head ∧
    (result head before after privateWords).stk (layout n (.inr 0)) = cells before ∧
    (result head before after privateWords).stk (layout n (.inl 0)) = cells after ∧
    (result head before after privateWords).stk (layout n (.inl 2)) = [] := by
  simp [result,BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
    NativeQueryExportAdapter.result,frame]

/-- No restriction is placed on independent private storage. -/
theorem private_retained {n : Nat} (head : Cell) (before after : List Cell)
    (privateWords : Fin n → List Bool) (i : Fin n) :
    (result head before after privateWords).stk (layout n (.inr i.succ)) =
      privateWords i := by
  simp [result,BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,frame]

/-- Actual framed execution has the unchanged derived clock and charge. -/
theorem charged {n : Nat} (head : Cell) (before after : List Cell)
    (privateWords : Fin n → List Bool) :
    ∃ charge ≤ NativeQueryExportAdapter.cost head after,
      BitOracleMachine.run (code n) (NativeQueryExportAdapter.clock head after)
        (initial head before after privateWords) =
          pure (result head before after privateWords,charge) := by
  obtain ⟨charge,hbound,hrun⟩ := NativeQueryExportAdapter.charged head after
  refine ⟨charge,hbound,?_⟩
  unfold code initial result
  rw [BitOracleStackFrame.run,hrun]
  rfl

end ExplainableCrypto.Helios.Computational.NativeQueryExportFrame
