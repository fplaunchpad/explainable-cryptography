import ExplainableCrypto.Helios.Computational.NativeAdaptiveCost
import ExplainableCrypto.Helios.Computational.NativeQueryExportFrame
import ExplainableCrypto.Helios.Computational.NativeRoundTripTheorem

/-! Typed concordance checks for the historical execution catalogue. -/
namespace ExplainableCrypto.Helios.Computational.FormalReference
open OracleComp OracleSpec

/-- Fixed native source, mechanically generated target, complete successful
native observation; no input-size or execution-certificate premise. -/
theorem native_compilation_display (before work input oldAnswer : List Bool) :
    (fun out => NativeAdaptiveRun.observe out.1) <$>
      BitOracleMachine.run NativeAdaptiveRun.program 19
        (NativeAdaptiveRun.start before work input oldAnswer) =
    some <$> NativeOracleTape.run NativeAdaptiveProbe.code 8
      (NativeAdaptiveProbe.start (NativeWordCompiler.tape before work)
        (OracleTapeOutput.wordTape oldAnswer) input) :=
  NativeAdaptiveRun.native_correspondence before work input oldAnswer

/-- Both hash reply lengths are bounded by the explicit adapter contract;
all allowed branches halt with this charge bound. -/
theorem native_reply_cost_display (before work input oldAnswer : List Bool) (limit : Nat) :
    BitOracleLoopBounded.Within limit
      (68+2*input.length+oldAnswer.length+3*limit)
      (BitOracleMachine.run NativeAdaptiveRun.program 19
        (NativeAdaptiveRun.start before work input oldAnswer)) :=
  NativeAdaptiveCost.within before work input oldAnswer limit

#print axioms native_compilation_display
#print axioms native_reply_cost_display
end ExplainableCrypto.Helios.Computational.FormalReference

namespace ExplainableCrypto.Helios.Computational.FormalReference
open OracleComp OracleSpec

/-- General cell heads and halves, not merely a dense fixed-program fixture.
The complete result retains native storage and arbitrary private words. -/
theorem native_query_export_display {n : Nat} (head : Option Bool)
    (before after : List (Option Bool)) (privateWords : Fin n → List Bool) :
    ∃ charge ≤ 12*after.length+36,
      BitOracleMachine.run (NativeQueryExportFrame.code n) (2*after.length+6)
        (NativeQueryExportFrame.initial head before after privateWords) =
      pure (NativeQueryExportFrame.result head before after privateWords,charge) := by
  have ht : NativeQueryExportAdapter.clock head after = 2*after.length+6 := by
    simp only [NativeQueryExportAdapter.clock,NativeQueryExport.clock,List.length_cons]
    omega
  have hc : NativeQueryExportAdapter.cost head after = 12*after.length+36 := by
    unfold NativeQueryExportAdapter.cost
    rw [ht]
    omega
  simpa only [ht,hc] using NativeQueryExportFrame.charged head before after privateWords

#print axioms native_query_export_display
end ExplainableCrypto.Helios.Computational.FormalReference

namespace ExplainableCrypto.Helios.Computational.FormalReference
open OracleComp OracleSpec

/-- One actual selected oracle command, complete framed result tree and derived
charge bound. Resident cell storage and arbitrary private words are explicit. -/
theorem native_roundtrip_display {l n : Nat} (p : NativeOracleTape.Code l)
    (q next : Fin l) (kind : OracleTapeDispatch.Kind)
    (h : Fin 3 → BitTapeCoverage.Cell)
    (before after : Fin 3 → List BitTapeCoverage.Cell)
    (limit : Nat) (privateWords : Fin n → List Bool)
    (hc : p q h = .oracle kind next) :
    (Prod.fst <$> NativeRoundTrip.framedExecute p q h before after limit privateWords =
      (fun reply => NativeRoundTrip.framedResult next h before after reply privateWords) <$>
        NativeRoundTrip.boundedCall limit kind (NativeRoundTrip.queryWord h after)) ∧
    (∀ out ∈ support (NativeRoundTrip.framedExecute p q h before after limit privateWords),
      out.2 ≤ NativeRoundTrip.callCost h before after limit) := by
  exact ⟨NativeRoundTrip.framed_correspondence p q next kind h before after limit privateWords hc,
    NativeRoundTrip.framed_cost p q next kind h before after limit privateWords hc⟩

#print axioms native_roundtrip_display
end ExplainableCrypto.Helios.Computational.FormalReference
