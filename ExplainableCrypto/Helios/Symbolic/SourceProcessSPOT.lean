import ExplainableCrypto.Helios.Symbolic.SourceProcessBinding
import ExplainableCrypto.Helios.Symbolic.SourcePayloadAgreement

namespace ExplainableCrypto.Helios.Symbolic.SourceProcessSPOT
open Historical General Source

abbrev receiver : Agent (Option Nat) :=
  .input 12 (.output 13 (.binary .pair (.var (some none))
    (.binary .pair (.var none) (.var (some (some 7))))) .nil)

/-- Receiving 40 leaves the next input and the previous free variable intact. -/
theorem process_input_does_not_capture :
    receiver.bind (.name 40) =
      .input 12 (.output 13 (.binary .pair (.name 40)
        (.binary .pair (.var none) (.var (some 7)))) .nil) := rfl

/-- Two different inputs occupy their independent positions in the output. -/
theorem process_nested_input_order :
    let inner : Agent (Option Nat) := .output 13 (.binary .pair (.name 40)
      (.binary .pair (.var none) (.var (some 7)))) .nil
    inner.bind (.name 41) =
      .output 13 (.binary .pair (.name 40) (.binary .pair (.name 41) (.var 7))) .nil := rfl

/-- A capture-all substitution produces a different complete continuation. -/
theorem capture_mutant_rejected :
    let p : Agent (Option Nat) := .output 13 (.binary .pair (.var none) (.var (some 7))) .nil
    p.bind (.name 40) ≠ p.subst (fun _ => .name 40) := by
  dsimp only
  intro h
  cases h

abbrev echo : Agent (Option Empty) := .output 9 (.var none) .nil
abbrev sent : Agent Empty := .output 9 (.name 40) .nil

/-- The communicated value remains observable in the receiver's continuation. -/
theorem communication_keeps_payload :
    Agent.CoreStep (.par (.output 8 (.name 40) .nil) (.input 8 echo)) (.par .nil sent) :=
  .comm _ _ _ _

/-- A different private channel cannot communicate, even through parallel rules. -/
theorem wrong_channel_cannot_communicate (r : Agent Empty) :
    ¬ Agent.CoreStep (.par (.output 8 (.name 40) .nil) (.input 10 echo)) r := by
  intro h
  have hh := (Agent.communication_coreStep_iff _ _ _ _ _ _).mp h
  omega

abbrev numericGuard : Formula Empty :=
  .equal (.binary .add (.const .zero) (.const .one)) (.const .one)

private theorem numeric_guard_holds : numericGuard.Holds Empty.elim :=
  .equation .zero_one

/-- Full E enables Then even though the two guard expressions differ literally. -/
theorem semantic_guard_then :
    Agent.CoreStep (.branch numericGuard sent .nil) sent ∧
    (Term.binary .add (.const .zero) (.const .one) : Ground) ≠ .const .one := by
  exact ⟨.thenBranch _ _ _ numeric_guard_holds,by decide⟩

/-- Syntactic inequality must not send this guard to the null branch. -/
theorem syntactic_guard_mutant_rejected :
    ¬ Agent.CoreStep (.branch numericGuard sent .nil) .nil := by
  intro h
  rcases (Agent.branch_coreStep_iff _ _ _ _).mp h with ⟨_,h⟩ | ⟨h,_⟩
  · cases h
  · exact h numeric_guard_holds

abbrev unequalGuard : Formula Empty :=
  .unequal (.binary .add (.const .zero) (.const .one)) (.const .one)

/-- E-equivalent terms falsify disequality, and a failed conjunct stops Then. -/
theorem failed_conjunction_else :
    Agent.CoreStep (.branch (.both numericGuard unequalGuard) sent .nil) .nil ∧
    ¬ Agent.CoreStep (.branch (.both numericGuard unequalGuard) sent .nil) sent := by
  have hf : ¬ (Formula.both numericGuard unequalGuard).Holds Empty.elim :=
    fun h => h.2 numeric_guard_holds
  refine ⟨.elseBranch _ _ _ hf,?_⟩
  intro h
  rcases (Agent.branch_coreStep_iff _ _ _ _).mp h with ⟨h,_⟩ | ⟨_,h⟩
  · exact hf h
  · cases h

/-- The literal trustee input body is reused by source process communication. -/
theorem trustee_communication (secret tallies : Ground) :
    Agent.CoreStep
      (.par (.output 8 tallies .nil) (.input 8 (.output 8 (trusteeBody (n := 1) secret) .nil)))
      (.par .nil (.output 8 (trusteeMessage (n := 1) secret tallies) .nil)) :=
  .comm _ _ _ _

/-- Result computation likewise binds the received partial tuple before output. -/
theorem result_communication (tallies partials : Ground) :
    Agent.CoreStep
      (.par (.output 8 partials .nil) (.input 8 (.output 9 (resultBody (n := 1) tallies) .nil)))
      (.par .nil (.output 9 (resultMessage (n := 1) tallies partials) .nil)) :=
  .comm _ _ _ _

end ExplainableCrypto.Helios.Symbolic.SourceProcessSPOT
