import ExplainableCrypto.Helios.Computational.NativeRoundTripStages

/-! The actual native event and the actual source event share one raw reply law.
Full successor states and exact event charges retain every original query/work
cell and replace only the answer with the received word. -/
namespace ExplainableCrypto.Helios.Computational.NativeRoundTrip
open Turing OracleComp OracleSpec
open BitTapeCoverage (Cell cells)
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

/-- Actual hash request or actual singleton coin reply. -/
def call (kind : OracleTapeDispatch.Kind) (query : List Bool) :
    OracleComp BitOracleMachine.spec (List Bool) := match kind with
  | .hash => liftM (BitOracleMachine.spec.query (.hash query))
  | .coin => do
      let bit ← liftM (BitOracleMachine.spec.query .coin)
      pure [bit]

def nativeSuccessor {l : Nat} (next : Fin l) (h : Fin 3 → Cell)
    (before after : Fin 3 → List Cell) (reply : List Bool) : NativeOracleTape.Config l :=
  ⟨some next,(nativeState next h before after).work,
    (nativeState next h before after).query,OracleTapeOutput.wordTape reply⟩

/-- The query decoder reads arbitrary native cells until its first blank. -/
theorem native_queryWord {l : Nat} (q : Fin l) (h : Fin 3 → Cell)
    (before after : Fin 3 → List Cell) :
    OracleTapeDispatch.readWord (nativeState q h before after).query = queryWord h after := by
  exact (NativeQueryReadWord.readWord (l := 0) none (h 1) (before 1) (after 1)).symm

/-- The original selected native oracle command, with the exact raw reply law
and complete native successor. Selection depends on the original native heads. -/
theorem native_call {l : Nat} (p : NativeOracleTape.Code l) (q next : Fin l)
    (kind : OracleTapeDispatch.Kind) (h : Fin 3 → Cell)
    (before after : Fin 3 → List Cell) (hc : p q h = .oracle kind next) :
    NativeOracleTape.step p (nativeState q h before after) = (do
      let reply ← call kind (queryWord h after)
      pure (nativeSuccessor next h before after reply)) := by
  have hs : p q (NativeOracleTape.heads (nativeState q h before after)) = .oracle kind next := by
    rw [nativeState_heads]
    exact hc
  cases kind with
  | hash =>
    rw [NativeOracleTape.hash_step p _ q next rfl hs,native_queryWord]
    rfl
  | coin =>
    rw [NativeOracleTape.coin_step p _ q next rfl hs]
    simp only [call,bind_assoc,pure_bind]
    rfl

def eventCost (kind : OracleTapeDispatch.Kind) (query oldAfter reply : List Bool) : Nat :=
  match kind with
  | .hash => 1+query.length+oldAfter.length+reply.length
  | .coin => 2+oldAfter.length

/-- The generated source issues that actual event and pays its actual dispatch
charge, including overwritten answer storage and the full hash reply. -/
theorem oracle_step {l : Nat} (p : NativeOracleTape.Code l) (next : Fin l)
    (kind : OracleTapeDispatch.Kind) (h : Fin 3 → Cell)
    (before after : Fin 3 → List Cell) :
    BitOracleMachine.step (code p) (oracleState next (kindIndex kind) h before after) = (do
      let reply ← call kind (queryWord h after)
      pure (replyState next (kindIndex kind) h before after reply,
        eventCost kind (queryWord h after) (cells (after 2)) reply)) := by
  unfold oracleState
  rw [exportResult_eq]
  cases kind with
  | hash =>
    simp [BitOracleMachine.step,TM2ReturnLink.embed,code_block,block,kindIndex,
      call,eventCost,replyState,oracleState,exportResult_eq,queryWord]
    rfl
  | coin =>
    simp [BitOracleMachine.step,TM2ReturnLink.embed,code_block,block,kindIndex,
      call,eventCost,replyState,oracleState,exportResult_eq]


/-- Every returned word has the actual native replacement-tape interpretation. -/
theorem result_represents_successor {l : Nat} (next : Fin l) (h : Fin 3 → Cell)
    (before after : Fin 3 → List Cell) (reply : List Bool) :
    Represents (result next h before after reply) (nativeSuccessor next h before after reply) :=
  result_represents next h before after reply

end ExplainableCrypto.Helios.Computational.NativeRoundTrip
