import ExplainableCrypto.Helios.Computational.TM1PrimitiveCost

/-! Literal controls for the unchanged primitive compiler. Expected tapes and
finite memory are stated independently; no arbitrary result encoder is used. -/
namespace ExplainableCrypto.Helios.Computational.TM1PrimitiveControls
open Turing TM1PrimitiveCost

private def code : Bool → TM1.Stmt Bool Bool Bool
  | false => .halt
  | true => .write (fun _ _ => true) (.move .right (.write (fun _ _ => true) .halt))

private def blank : Tape Bool := Tape.mk₁ []

/-- The literal program writes both cells and stops at the second one. -/
theorem physical_writes :
    (tick code)^[4] ⟨(some (code true), false), blank⟩ =
      ⟨(none, false), Tape.mk' (ListBlank.mk [true]) (ListBlank.mk [true])⟩ := by
  rfl

/-- Counting a whole TM1 statement as one primitive transition loses writes. -/
theorem one_tick_is_insufficient :
    ((tick code)^[1] ⟨(some (code true), false), blank⟩).Tape.1 = true ∧
    ((tick code)^[1] ⟨(some (code true), false), blank⟩).Tape.left.nth 0 = false := by
  exact ⟨rfl, rfl⟩

private def conditional : TM1.Stmt Bool Bool Bool :=
  .load (fun _ _ => true) (.branch (fun _ v => v)
    (.write (fun _ v => v) .halt) (.move .left .halt))

/-- Finite load/branch evaluation selects the write, with two physical ticks. -/
theorem finite_branch :
    work conditional false blank = 2 ∧
    (tick code)^[2] ⟨(some conditional, false), blank⟩ =
      ⟨(none, true), Tape.mk₁ [true]⟩ := by
  exact ⟨rfl, rfl⟩

/-- Even empty halt emits the compiler's final identity write. -/
theorem halt_needs_one :
    work (TM1.Stmt.halt : TM1.Stmt Bool Bool Bool) false blank = 1 ∧
    (tick code)^[1] ⟨(some .halt, false), blank⟩ = ⟨(none, false), blank⟩ ∧
    (tick code)^[0] ⟨(some .halt, false), blank⟩ ≠ ⟨(none, false), blank⟩ := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  have := congrArg (fun c : TM0.Cfg Bool (TM1to0.Λ' code) => c.q.1.isNone) h
  contradiction

/-- A smaller support is valid for its entry, but gives no bound at an excluded
label. This rules out silently applying the multiplier to arbitrary states. -/
theorem support_is_required :
    TM1.Supports code {false} ∧
    multiplier code {false} = 1 ∧
    work (code true) false blank = 4 ∧
    ¬ (some true ∈ Finset.insertNone ({false} : Finset Bool)) := by
  refine ⟨?_, ?_, rfl, by decide⟩
  · constructor
    · exact Finset.mem_singleton_self _
    · intro label h
      have := Finset.mem_singleton.mp h
      subst label
      trivial
  · simp [multiplier, code, allowance]

/-- Goto preserves its next live statement in the primitive control. -/
theorem goto_preserves_next :
    (tick code)^[1] ⟨(some (.goto (fun _ _ => true)), false), blank⟩ =
      ⟨(some (code true), false), blank⟩ := rfl

end ExplainableCrypto.Helios.Computational.TM1PrimitiveControls
