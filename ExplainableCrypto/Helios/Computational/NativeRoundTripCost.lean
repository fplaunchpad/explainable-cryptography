import ExplainableCrypto.Helios.Computational.NativeRoundTripCorrectness
import ExplainableCrypto.Helios.Computational.NativeRoundTripBounds

/-! The complete observed native call has a derived uniform source charge.
The only reply condition is the existing bounded hash interface; both coin
values remain available. This is a live-return bound, not a source-halt claim. -/
namespace ExplainableCrypto.Helios.Computational.NativeRoundTrip
open Turing OracleComp OracleSpec
open BitTapeCoverage (Cell cells)
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

/-- Actual export, event, replacement, and continuation-return instructions
supply the complete source charge on every allowed branch. -/
theorem execution_cost {l : Nat} (p : NativeOracleTape.Code l) (q next : Fin l)
    (kind : OracleTapeDispatch.Kind) (h : Fin 3 → Cell) (before after : Fin 3 → List Cell)
    (limit : Nat) (hc : p q h = .oracle kind next) :
    ∀ out ∈ support (boundedExecute p q h before after limit),
      out.2 ≤ callCost h before after limit := by
  obtain ⟨fuel,hfuel,charge,hcharge,he⟩ :=
    execution_decomposition p q next kind h before after limit hc
  intro out ho
  rw [he] at ho
  obtain ⟨reply,hr,ho⟩ := OracleComp.mem_support_bind_peel _ _ ho
  have hlength := boundedCall_length limit kind (queryWord h after) reply hr
  obtain ⟨last,hlast,hpost⟩ := suffix p next (kindIndex kind) h before after reply
    (limit+1) fuel hlength hfuel
  rw [hpost,simulateQ_pure] at ho
  simp only [pure_bind] at ho
  have hout := OracleComp.eq_of_mem_support_pure _ ho
  rw [hout]
  have hevent := eventCost_le limit kind (queryWord h after) (cells (after 2)) reply hlength
  dsimp only
  unfold callCost
  omega

end ExplainableCrypto.Helios.Computational.NativeRoundTrip
