import ExplainableCrypto.Helios.Computational.NativeWordCompiler
import ExplainableCrypto.Helios.Computational.NativeAdaptiveProbe
import ExplainableCrypto.Helios.Computational.NativeAdaptiveRun
import ExplainableCrypto.Helios.Computational.BitOraclePrimitiveBounded

/-! Derived charges for the bounded native adaptive compiler experiment.
The independently executed finite gate passed before these general bounds.
The local bound concerns actual generated syntax, including guarded branches. -/
namespace ExplainableCrypto.Helios.Computational.NativeAdaptiveCost
open OracleComp OracleSpec
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

def localBound (command : BitOracleMachine.Command 6 495 27) : Prop :=
  match command with
  | .compute stmt => BitOracleMachine.localCost stmt ≤ 5
  | .coin _ _ | .hash _ _ _ => True

instance (command : BitOracleMachine.Command 6 495 27) : Decidable (localBound command) := by
  cases command <;> unfold localBound <;> infer_instance

/-- All 495 generated labels satisfy the same bound; no syntax cost is supplied
as a hypothesis. The three executed oracle events are charged by the oracle rules. -/
theorem generated_local_bound : ∀ label : Fin 495,
    localBound (NativeWordCompiler.code NativeAdaptiveProbe.code label) := by
  decide +kernel

def charge (input oldAnswer firstReply : List Bool) (coin : Bool)
    (secondReply : List Bool) : Nat :=
  66 + input.length + oldAnswer.length + 2*firstReply.length +
    (NativeAdaptiveProbe.dependentWord input firstReply coin).length + secondReply.length

def bound (input oldAnswer : List Bool) (limit : Nat) : Nat :=
  68 + 2*input.length + oldAnswer.length + 3*limit

/-- Only the two hash replies require the explicit encoded-answer size limit;
coins remain unrestricted and private work length does not enter the charge. -/
theorem charge_le (input oldAnswer firstReply : List Bool) (coin : Bool)
    (secondReply : List Bool) (limit : Nat)
    (hfirst : firstReply.length ≤ limit) (hsecond : secondReply.length ≤ limit) :
    charge input oldAnswer firstReply coin secondReply ≤ bound input oldAnswer limit := by
  simp only [charge,bound,NativeAdaptiveProbe.dependentWord,List.length_append,
    List.length_cons,List.length_nil,List.length_drop]
  omega

/-- Distinct fixed positive charge; the copied private words do not affect it. -/
theorem literal_charge : charge [false,true,true,false,true] [true,false,true]
    [true,false] true [false,true,false] = 86 := by decide +kernel

/-- The first hash overwrites the old answer, so omitting its length is false. -/
theorem old_answer_cost_matters :
    charge [] [true,false,true] [] false [] ≠ charge [] [] [] false [] := by decide +kernel

/-- Every branch of the exact source tree halts and meets the derived bound. -/
theorem expected_within (before work input oldAnswer : List Bool) (limit : Nat) :
    BitOracleLoopBounded.Within limit (bound input oldAnswer limit)
      (NativeAdaptiveRun.expected before work input oldAnswer) := by
  change ∀ firstReply : List Bool, firstReply.length ≤ limit →
    ∀ coin : Bool, True → ∀ secondReply : List Bool, secondReply.length ≤ limit →
      (NativeAdaptiveRun.finish before work input firstReply coin secondReply).l = none ∧
        charge input oldAnswer firstReply coin secondReply ≤ bound input oldAnswer limit
  intro firstReply hfirst coin _ secondReply hsecond
  exact ⟨rfl, charge_le input oldAnswer firstReply coin secondReply limit hfirst hsecond⟩

/-- The bound is obtained from the actual generated run, with no supplied cost
certificate or execution correspondence premise. -/
theorem within (before work input oldAnswer : List Bool) (limit : Nat) :
    BitOracleLoopBounded.Within limit (bound input oldAnswer limit)
      (BitOracleMachine.run NativeAdaptiveRun.program 19
        (NativeAdaptiveRun.start before work input oldAnswer)) := by
  rw [NativeAdaptiveRun.exact_run]
  exact expected_within before work input oldAnswer limit

/-- Existing primitive lowering preserves the entire adaptive tree at a derived
clock. Its entry is an explicitly loaded resident state; startup is not claimed. -/
theorem physical_run (before work input oldAnswer : List Bool) (limit : Nat)
    (previous : List Bool) (physicalOldAnswer : Turing.Tape (Option Bool)) :
    let cfg := NativeAdaptiveRun.start before work input oldAnswer
    let cap := TM2TapeRuns.height cfg.stk + bound input oldAnswer limit + previous.length
    let clock := BitOracleTapeCap.unitCost cap * bound input oldAnswer limit
    BitOraclePrimitiveBounded.observe <$>
      simulateQ (BitOracleLoopBounded.adapter limit)
        (BitOraclePrimitiveLoop.run NativeAdaptiveRun.program
          (clock * BitOraclePrimitiveLoop.globalFactor NativeAdaptiveRun.program)
          (BitOraclePrimitiveLoop.lower NativeAdaptiveRun.program
            (BitOracleTapeLoop.ready cfg (OracleTapeOutput.wordTape previous) physicalOldAnswer))) =
      (fun out => some out.1) <$> simulateQ (BitOracleLoopBounded.adapter limit)
        (NativeAdaptiveRun.expected before work input oldAnswer) := by
  simpa only [NativeAdaptiveRun.exact_run] using
    BitOraclePrimitiveBounded.run_source_bounded NativeAdaptiveRun.program 19 limit
      (bound input oldAnswer limit) (NativeAdaptiveRun.start before work input oldAnswer)
      previous physicalOldAnswer (within before work input oldAnswer limit)

end ExplainableCrypto.Helios.Computational.NativeAdaptiveCost
