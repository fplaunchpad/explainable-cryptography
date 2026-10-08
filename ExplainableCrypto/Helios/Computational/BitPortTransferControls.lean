import ExplainableCrypto.Helios.Computational.BitOraclePortTransfer
import Mathlib.Data.Fin.VecNotation

/-! Literal order, erasure, finite-memory and workspace controls for actual port movement. -/
namespace ExplainableCrypto.Helios.Computational.BitPortTransferControls
open BitCopyMachine.Stack

/-- Replacement keeps source order and removes an old destination suffix. -/
theorem overwrite :
    let out := (BitPortTransfer.tick false)^[9]
      (BitPortTransfer.config (some .clear) [true, false] [true] [])
    out.l = none ∧ out.stk source = [true, false] ∧
      out.stk destination = [true, false] ∧ out.stk scratch = [] := by
  decide +kernel

/-- Inbound transfer additionally erases its private source word. -/
theorem consumed_private_word :
    let out := (BitPortTransfer.tick true)^[11]
      (BitPortTransfer.config (some .clear) [true, false] [true] [])
    out.l = none ∧ out.stk source = [] ∧
      out.stk destination = [true, false] ∧ out.stk scratch = [] := by
  decide +kernel

private def caller : BitOracleMachine.Config 3 4 7 :=
  ⟨some 0, 6, ![[false], [true, false], [false, true, true]]⟩

/-- Actual caller memory and other stacks survive, including a nonempty destination. -/
theorem caller_frame :
    let out := (TM2ReturnLink.tick (BitOraclePortTransfer.program (l := 4) (m := 7) 1))^[15]
      (BitOraclePortTransfer.start caller 1 2 [true, false, true])
    out.l = none ∧ out.var.1 = (2, 6) ∧
      out.stk (.inl 0) = [false] ∧ out.stk (.inl 1) = [true, false, true] ∧
      out.stk (.inl 2) = [false, true, true] ∧ out.stk (.inr false) = [] ∧
      out.stk (.inr true) = [] := by
  decide +kernel

/-- A request may use the same caller port later overwritten by its answer. -/
theorem aliased_request_and_answer :
    ∃ before ≤ 8,
      let issued := (TM2ReturnLink.tick (BitOraclePortTransfer.requestProgram (l := 4) (m := 7) 1))^[before]
        (BitOraclePortTransfer.requestStart caller 1 2 [])
      issued.l = none ∧ issued.stk (.inr false) = [true, false] ∧
      ∀ answer : List Bool, ∃ after,
        before + 1 + after ≤ 9 * (5 + answer.length) ∧
        let out := (TM2ReturnLink.tick (BitOraclePortTransfer.program (l := 4) (m := 7) 1))^[after]
          (BitOraclePortTransfer.deliver answer issued)
        out.l = none ∧ BitOraclePortTransfer.project out = BitOracleMachine.resume caller 1 2 answer ∧
          out.stk (.inr false) = [] ∧ out.stk (.inr true) = [] :=
  BitOraclePortTransfer.hash_transfer caller 1 1 2

/-- A stale private port cannot be treated as cost-free empty workspace. -/
theorem uncleared_port_not_free :
    let cfg : BitOracleMachine.Config 1 1 1 := ⟨some 0, 0, fun _ => []⟩
    let out := (TM2ReturnLink.tick (BitOraclePortTransfer.requestProgram (l := 1) (m := 1) 0))^[9]
      (BitOraclePortTransfer.requestStart cfg 0 0 (List.replicate 10 true))
    out.l = some .clear ∧ out.stk (.inr false) = [true] := by
  decide +kernel

/-- Scratch freshness is necessary and is supplied by the constructed starts. -/
theorem dirty_scratch_changes_word :
    let out := (BitPortTransfer.tick false)^[10]
      (BitPortTransfer.config (some .clear) [true, false] [true] [true])
    out.stk destination = [true, true, false] ∧ out.stk destination ≠ [true, false] := by
  decide +kernel

end ExplainableCrypto.Helios.Computational.BitPortTransferControls
