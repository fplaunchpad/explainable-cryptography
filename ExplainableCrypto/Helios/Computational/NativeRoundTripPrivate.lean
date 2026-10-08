import ExplainableCrypto.Helios.Computational.NativeRoundTripExecution

/-! The concrete one-call executor with arbitrary independent private stacks.
One real entry step precedes the bounded native-return observation; framing
preserves the exact event tree, live result and every accumulated charge. -/
namespace ExplainableCrypto.Helios.Computational.NativeRoundTrip
open Turing OracleComp OracleSpec
open BitTapeCoverage (Cell cells)
variable {l n : Nat}
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

def framedLayout (n : Nat) : Fin 8 ⊕ Fin n ≃ Fin (8+n) := finSumFinEquiv

def framedCode (p : NativeOracleTape.Code l) (n : Nat) :=
  BitOracleStackFrame.code (framedLayout n) (code p)

def framedInitial (q : Fin l) (h : Fin 3 → Cell) (before after : Fin 3 → List Cell)
    (privateWords : Fin n → List Bool) :=
  BitOracleStackFrame.embed (framedLayout n) (initial q h before after) privateWords

def framedResult (next : Fin l) (h : Fin 3 → Cell) (before after : Fin 3 → List Cell)
    (reply : List Bool) (privateWords : Fin n → List Bool) :=
  BitOracleStackFrame.embed (framedLayout n) (result next h before after reply) privateWords

/-- The same actual first step and bounded live-return observation are executed
on the larger machine; private words are never extracted by a host callback. -/
def framedExecute (p : NativeOracleTape.Code l) (q : Fin l) (h : Fin 3 → Cell)
    (before after : Fin 3 → List Cell) (limit : Nat) (privateWords : Fin n → List Bool) :=
  simulateQ (BitOracleLoopBounded.adapter limit) (do
    let first ← BitOracleMachine.step (framedCode p n)
      (framedInitial q h before after privateWords)
    let last ← NativeReturnObservation.run atNative (framedCode p n)
      (callFuel h before after limit) first.1
    pure (last.1,first.2+last.2))

private theorem execute_frame (p : NativeOracleTape.Code l) (fuel : Nat)
    (cfg : Config l) (privateWords : Fin n → List Bool) :
    (do let first ← BitOracleMachine.step (framedCode p n)
          (BitOracleStackFrame.embed (framedLayout n) cfg privateWords)
        let last ← NativeReturnObservation.run atNative (framedCode p n) fuel first.1
        pure (last.1,first.2+last.2)) =
      (fun out => (BitOracleStackFrame.embed (framedLayout n) out.1 privateWords,out.2)) <$>
        execute p fuel cfg := by
  unfold framedCode execute
  rw [BitOracleStackFrame.step]
  simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
  apply bind_congr
  intro first
  rw [NativeReturnObservation.stackFrame_run]
  simp [map_eq_bind_pure_comp,bind_assoc]

/-- Exact full-state/query-tree transport through the same bounded adapter,
including charge. The theorem imposes no condition on private storage. -/
theorem framed_execution (p : NativeOracleTape.Code l) (q : Fin l) (h : Fin 3 → Cell)
    (before after : Fin 3 → List Cell) (limit : Nat) (privateWords : Fin n → List Bool) :
    framedExecute p q h before after limit privateWords =
      (fun out => (BitOracleStackFrame.embed (framedLayout n) out.1 privateWords,out.2)) <$>
        boundedExecute p q h before after limit := by
  unfold framedExecute framedInitial boundedExecute
  rw [execute_frame,simulateQ_map]

theorem framedResult_private_retained (next : Fin l) (h : Fin 3 → Cell)
    (before after : Fin 3 → List Cell) (reply : List Bool) (privateWords : Fin n → List Bool)
    (i : Fin n) :
    (framedResult next h before after reply privateWords).stk (framedLayout n (.inr i)) =
      privateWords i := by
  simp [framedResult,BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data]

theorem framedResult_base (next : Fin l) (h : Fin 3 → Cell)
    (before after : Fin 3 → List Cell) (reply : List Bool) (privateWords : Fin n → List Bool)
    (i : Fin 8) :
    (framedResult next h before after reply privateWords).stk (framedLayout n (.inl i)) =
      (result next h before after reply).stk i := by
  simp [framedResult,BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data]

theorem framedResult_memory (next : Fin l) (h : Fin 3 → Cell)
    (before after : Fin 3 → List Cell) (reply : List Bool) (privateWords : Fin n → List Bool) :
    (framedResult next h before after reply privateWords).var =
      memory ![h 0,h 1,reply.head?] := rfl

theorem framedResult_live (next : Fin l) (h : Fin 3 → Cell)
    (before after : Fin 3 → List Cell) (reply : List Bool) (privateWords : Fin n → List Bool) :
    (framedResult next h before after reply privateWords).l = some (entryLabel next) := rfl

end ExplainableCrypto.Helios.Computational.NativeRoundTrip
