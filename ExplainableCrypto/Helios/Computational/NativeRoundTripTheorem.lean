import ExplainableCrypto.Helios.Computational.NativeRoundTripCorrectness
import ExplainableCrypto.Helios.Computational.NativeRoundTripCost
import ExplainableCrypto.Helios.Computational.NativeRoundTripPrivate

/-! General one-call native oracle compilation, with arbitrary private storage.
The actual code selects the event and continuation from the original heads,
exports the resident query, replaces both answer halves, and returns live.
The hash interface imposes an explicit reply length limit. -/
namespace ExplainableCrypto.Helios.Computational.NativeRoundTrip
open Turing OracleComp OracleSpec
open BitTapeCoverage (Cell cells)
variable {l n : Nat}
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

/-- Exact event-tree and full resident state correspondence for the actual
framed controller. Private stacks, work/query cells, scratch and the live
continuation are fixed by the complete result, for every permitted reply. -/
theorem framed_correspondence (p : NativeOracleTape.Code l) (q next : Fin l)
    (kind : OracleTapeDispatch.Kind) (h : Fin 3 → Cell) (before after : Fin 3 → List Cell)
    (limit : Nat) (privateWords : Fin n → List Bool)
    (hc : p q h = .oracle kind next) :
    Prod.fst <$> framedExecute p q h before after limit privateWords =
      (fun reply => framedResult next h before after reply privateWords) <$>
        boundedCall limit kind (queryWord h after) := by
  rw [framed_execution]
  have he := congrArg (fun tree => (fun cfg =>
    BitOracleStackFrame.embed (framedLayout n) cfg privateWords) <$> tree)
    (execution_correspondence p q next kind h before after limit hc)
  simpa [Functor.map_map,Function.comp_def,framedResult] using he

/-- Every actual allowed branch has the instruction-derived combined charge;
no supplied cost certificate or source halt is assumed. -/
theorem framed_cost (p : NativeOracleTape.Code l) (q next : Fin l)
    (kind : OracleTapeDispatch.Kind) (h : Fin 3 → Cell) (before after : Fin 3 → List Cell)
    (limit : Nat) (privateWords : Fin n → List Bool)
    (hc : p q h = .oracle kind next) :
    ∀ out ∈ support (framedExecute p q h before after limit privateWords),
      out.2 ≤ callCost h before after limit := by
  intro out ho
  rw [framed_execution,map_eq_bind_pure_comp] at ho
  obtain ⟨base,hbase,hout⟩ := OracleComp.mem_support_bind_peel _ _ ho
  have he := OracleComp.eq_of_mem_support_pure _ hout
  rw [he]
  exact execution_cost p q next kind h before after limit hc base hbase

end ExplainableCrypto.Helios.Computational.NativeRoundTrip
