import ExplainableCrypto.Helios.Computational.NativeRoundTripCode
import ExplainableCrypto.Helios.Computational.NativeRoundTripFrames
import ExplainableCrypto.Helios.Computational.NativeReturnObservation

namespace ExplainableCrypto.Helios.Computational.NativeRoundTrip
open Turing OracleComp OracleSpec
open BitTapeCoverage (Cell cellCode readCell cells)
open NativeRoundTripMemory (pack unpack)
set_option maxRecDepth 32768
set_option maxHeartbeats 900000

variable {l : Nat}
def queryWord (h : Fin 3 → Cell) (after : Fin 3 → List Cell) := NativeQueryExport.wordPrefix (h 1::after 1)
def blockStart (next : Fin l) (kind : Fin 2) (h : Fin 3 → Cell) (before after : Fin 3 → List Cell) : Config l :=
  ⟨some (blockLabel next kind 0),memory h,words before after⟩
def oracleState (next : Fin l) (kind : Fin 2) (h : Fin 3 → Cell) (before after : Fin 3 → List Cell) : Config l :=
  TM2ReturnLink.embed (exportLabel next kind) (blockLabel next kind 5) (exportResult h before after)
def replyState (next : Fin l) (kind : Fin 2) (h : Fin 3 → Cell) (before after : Fin 3 → List Cell) (reply : List Bool) : Config l :=
  BitOracleMachine.resume (oracleState next kind h before after) 5 (blockLabel next kind 6) reply

theorem entry_step (p : NativeOracleTape.Code l) (q next : Fin l) (kind : OracleTapeDispatch.Kind)
    (h : Fin 3 → Cell) (before after : Fin 3 → List Cell) (hc : p q h = .oracle kind next) :
    BitOracleMachine.step (code p) (initial q h before after) =
      pure (blockStart next (kindIndex kind) h before after,2) := by
  simp [BitOracleMachine.step,initial,code_entry,entry,currentHeads_memory,hc,
    BitOracleMachine.localCost,TM2.stepAux,blockStart]

theorem prepare_export (p : NativeOracleTape.Code l) (next : Fin l) (kind : Fin 2)
    (h : Fin 3 → Cell) (before after : Fin 3 → List Cell) :
    BitOracleMachine.step (code p) (blockStart next kind h before after) =
      pure (TM2ReturnLink.embed (exportLabel next kind) (blockLabel next kind 5)
        (exportInitial h before after),2) := by
  rw [exportInitial_eq]
  simp [BitOracleMachine.step,blockStart,code_block,block,TM2.stepAux,
    BitOracleMachine.localCost,TM2ReturnLink.embed,exportLabel,
    memory,currentHeads,NativeRoundTripMemory.unpack_pack,heads_headsCode]

theorem replyState_eq (next : Fin l) (kind : Fin 2) (h : Fin 3 → Cell)
    (before after : Fin 3 → List Cell) (reply : List Bool) :
    replyState next kind h before after reply =
      ⟨some (blockLabel next kind 6),pack (headsCode h) (cellCode (h 1)),
        ![cells (before 0),cells (after 0),cells (before 1),cells (after 1),
          cells (before 2),reply,queryWord h after,[]]⟩ := by
  unfold replyState oracleState
  rw [exportResult_eq]
  apply congrArg (fun xs : Fin 8 → List Bool =>
    (⟨some (blockLabel next kind 6),pack (headsCode h) (cellCode (h 1)),xs⟩ : Config l))
  funext k
  fin_cases k <;> simp [TM2ReturnLink.embed,Function.update,queryWord]

theorem prepare_import (p : NativeOracleTape.Code l) (next : Fin l) (kind : Fin 2)
    (h : Fin 3 → Cell) (before after : Fin 3 → List Cell) (reply : List Bool) :
    BitOracleMachine.step (code p) (replyState next kind h before after reply) =
      pure (TM2ReturnLink.embed (importLabel next kind) (blockLabel next kind 12)
        (importInitial h before after reply (queryWord h after)),2) := by
  rw [replyState_eq,importInitial_eq]
  simp [BitOracleMachine.step,code_block,block,TM2.stepAux,BitOracleMachine.localCost,
    TM2ReturnLink.embed,importLabel,NativeRoundTripMemory.unpack_pack]

private theorem read_code (c : Cell) : readCell (cellCode c) = c := by
  cases c with | none => rfl | some b => cases b <;> rfl

theorem finish_import (p : NativeOracleTape.Code l) (next : Fin l) (kind : Fin 2)
    (h : Fin 3 → Cell) (before after : Fin 3 → List Cell) (reply : List Bool) :
    BitOracleMachine.step (code p)
      (TM2ReturnLink.embed (importLabel next kind) (blockLabel next kind 12)
        (importResult h before after reply)) = pure (result next h before after reply,2) := by
  rw [importResult_eq]
  simp [BitOracleMachine.step,TM2ReturnLink.embed,code_block,block,TM2.stepAux,
    BitOracleMachine.localCost,currentHeads,localMemory,NativeRoundTripMemory.unpack_pack,
    heads_headsCode,read_code,result]

end ExplainableCrypto.Helios.Computational.NativeRoundTrip
