import ExplainableCrypto.Helios.Computational.NativeRoundTripStages

namespace ExplainableCrypto.Helios.Computational.NativeRoundTrip
open Turing OracleComp OracleSpec
open BitTapeCoverage (Cell cellCode readCell cells)
set_option maxRecDepth 32768
set_option maxHeartbeats 900000
variable {l : Nat}

def exportClock (h : Fin 3 → Cell) (after : Fin 3 → List Cell) :=
  NativeQueryExportAdapter.clock (h 1) (after 1)
def importClock (h : Fin 3 → Cell) (before after : Fin 3 → List Cell) (width : Nat) :=
  (cells (before 2)).length+(queryWord h after).length+2*width+5

/-- Exact prefix to the oracle event. The exporter supplies its own frame,
head preparation, instruction matching and cost; no live padding is used. -/
theorem export_prefix (p : NativeOracleTape.Code l) (next : Fin l) (kind : Fin 2)
    (h : Fin 3 → Cell) (before after : Fin 3 → List Cell) :
    ∃ used ≤ exportClock h after+1, ∃ charge ≤ 2+6*exportClock h after,
      NativeReturnObservation.run atNative (code p) used (blockStart next kind h before after) =
        pure (oracleState next kind h before after,charge) := by
  obtain ⟨used,hu,charge,hcharge,hr⟩ := NativeReturnObservation.live_prefix
    exportProgram (code p) (exportLabel next kind) (blockLabel next kind 5)
    atNative (fun phase => atNative_block next kind _) (code_export p next kind)
    6 export_local_cost (exportClock h after) (exportInitial h before after)
    (by rw [show exportClock h after = NativeQueryExportAdapter.clock (h 1) (after 1) from rfl,
      export_source_run]; rw [exportResult_eq])
  change (NativeReturnObservation.run atNative (code p) used _ = _) at hr
  rw [show exportClock h after = NativeQueryExportAdapter.clock (h 1) (after 1) from rfl,
    export_source_run] at hr
  refine ⟨used+1,by omega,2+charge,by omega,?_⟩
  rw [NativeReturnObservation.run_succ_unstopped _ _ _ _
    (show NativeReturnObservation.stopped atNative (blockStart next kind h before after) = false
      from atNative_block next kind 0),prepare_export]
  simp only [pure_bind]
  rw [hr]
  rfl

/-- Actual reply conversion and return at any sufficient observation clock.
The final native entry is live. Extra observation fuel does not execute it. -/
theorem suffix (p : NativeOracleTape.Code l) (next : Fin l) (kind : Fin 2)
    (h : Fin 3 → Cell) (before after : Fin 3 → List Cell) (reply : List Bool)
    (width fuel : Nat) (hw : reply.length ≤ width)
    (hf : importClock h before after width+2 ≤ fuel) :
    ∃ charge ≤ 4+5*importClock h before after width,
      NativeReturnObservation.run atNative (code p) fuel (replyState next kind h before after reply) =
        pure (result next h before after reply,charge) := by
  let clock := NativeAnswerImport.clock (cells (before 2)) reply (queryWord h after)
  have hc : clock ≤ importClock h before after width := by
    dsimp [clock,NativeAnswerImport.clock,importClock]
    omega
  obtain ⟨used,hu,charge,hcharge,hr⟩ := NativeReturnObservation.live_prefix
    importProgram (code p) (importLabel next kind) (blockLabel next kind 12)
    atNative (fun phase => atNative_block next kind _) (code_import p next kind)
    5 import_local_cost clock (importInitial h before after reply (queryWord h after))
    (by rw [import_source_run]; rw [importResult_eq])
  rw [import_source_run] at hr
  have finish : NativeReturnObservation.run atNative (code p) 1
      (TM2ReturnLink.embed (importLabel next kind) (blockLabel next kind 12)
        (importResult h before after reply)) = pure (result next h before after reply,2) := by
    rw [NativeReturnObservation.run_succ_unstopped _ _ _ _
      (show NativeReturnObservation.stopped atNative
        (TM2ReturnLink.embed (importLabel next kind) (blockLabel next kind 12)
          (importResult h before after reply)) = false from atNative_block next kind 12),
      finish_import]
    simp [NativeReturnObservation.run]
  have imported : NativeReturnObservation.run atNative (code p) (used+1)
      (TM2ReturnLink.embed (importLabel next kind) (blockLabel next kind 12)
        (importInitial h before after reply (queryWord h after))) =
        pure (result next h before after reply,charge+2) := by
    rw [NativeReturnObservation.run_add,hr]
    simp [finish]
  have full : NativeReturnObservation.run atNative (code p) (used+2)
      (replyState next kind h before after reply) = pure (result next h before after reply,2+(charge+2)) := by
    rw [show used+2 = (used+1)+1 by omega,NativeReturnObservation.run_succ_unstopped _ _ _ _
      (show NativeReturnObservation.stopped atNative (replyState next kind h before after reply) = false from
        atNative_block next kind 6),prepare_import]
    simp only [pure_bind]
    rw [imported]
    rfl
  have le : used+2 ≤ fuel := by omega
  refine ⟨2+(charge+2),by omega,?_⟩
  have pad := NativeReturnObservation.stopped_padding atNative (code p) (used+2) (fuel-(used+2))
    _ _ _ full (show NativeReturnObservation.stopped atNative (result next h before after reply) = true
      from atNative_entry next)
  simpa only [Nat.add_sub_of_le le] using pad

end ExplainableCrypto.Helios.Computational.NativeRoundTrip
