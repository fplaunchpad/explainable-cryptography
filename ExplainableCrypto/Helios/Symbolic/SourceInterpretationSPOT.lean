import ExplainableCrypto.Helios.Symbolic.SourceInterpretationFrames
import ExplainableCrypto.Helios.Symbolic.SourceWellFormedSPOT
import ExplainableCrypto.Helios.Symbolic.SourceFrameInternal

namespace ExplainableCrypto.Helios.Symbolic.SourceInterpretationSPOT
open Historical General Source Extended

abbrev wrapped : Ground := .unary .fst (.binary .pair (.const .one) (.name 40))
abbrev outOne : Agent Empty := .output 9 (.const .one) .nil
abbrev outWrapped : Agent Empty := .output 9 wrapped .nil

theorem projected_payload_equivalent : Agent.EquivE outWrapped outOne ∧ wrapped ≠ .const .one :=
  ⟨.output 9 (.equation (.fst _ _)) .nil,by decide⟩

theorem bits_not_collapsed :
    ¬ Agent.EquivE (.output 9 (.const .zero) .nil : Agent Empty) outOne := by
  intro h
  cases h with
  | output _ hm _ => exact zero_not_one hm

theorem channel_change_rejected :
    ¬ Agent.EquivE outOne (.output 8 (.const .one) .nil) := by intro h; cases h

theorem guard_polarity_rejected :
    ¬ Formula.EquivE (.equal wrapped (.const .one)) (.unequal (.const .one) (.const .one)) := by
  intro h
  cases h

abbrev wrappedGuard : Formula Empty :=
  .both (.equal wrapped (.const .one)) (.unequal (.const .one) (.const .one))
abbrev reducedGuard : Formula Empty :=
  .both (.equal (.const .one) (.const .one)) (.unequal (.const .one) (.const .one))

/-- A true equality conjunct does not rescue a false disequality conjunct. -/
theorem negative_conjunct_preserved :
    Formula.EquivE wrappedGuard reducedGuard ∧
    Agent.CoreStep (.branch wrappedGuard outOne .nil) .nil ∧
    Agent.CoreStep (.branch reducedGuard outOne .nil) .nil := by
  exact ⟨.both (.equal (.equation (.fst _ _)) (.refl _)) (.unequal (.refl _) (.refl _)),
    .elseBranch _ _ _ (fun h => h.2 (.refl _)),
    .elseBranch _ _ _ (fun h => h.2 (.refl _))⟩

abbrev nestedReceiver : Agent (Option Empty) :=
  .input 10 (.output 9 (.binary .pair (.var (some none)) (.var none)) .nil)

/-- The old received message changes modulo E; the next input stays fresh. -/
theorem nested_input_keeps_binders :
    Agent.EquivE (nestedReceiver.bind wrapped)
      (.input 10 (.output 9 (.binary .pair (.const .one) (.var none)) .nil)) ∧
    nestedReceiver.bind (.const .one) =
      .input 10 (.output 9 (.binary .pair (.const .one) (.var none)) .nil) := by
  exact ⟨(Agent.EquivE.refl nestedReceiver).bind (.equation (.fst _ _)),rfl⟩

theorem communication_transports_full_receiver :
    ∃ q, Agent.CoreStep
      (.par (.output 8 (.const .one) .nil) (.input 8 nestedReceiver)) q ∧
      Agent.EquivE (.par .nil (nestedReceiver.bind wrapped)) q := by
  exact (Agent.CoreStep.comm 8 wrapped .nil nestedReceiver).equivE_transport
    (.par (.output 8 (.equation (.fst _ _)) .nil) (.refl _))

/-- Reordering and removing Nil can be combined with payload replacement. -/
theorem parallel_and_equational_composite :
    Agent.EvalEq (.par .nil outWrapped) outOne :=
  (Agent.EvalEq.of_parEq ((Agent.ParEq.comm _ _).trans (.zero _))).trans
    (.of_equivE projected_payload_equivalent.1)

/-- E-equivalent output payloads need not have identical literal labels. -/
theorem literal_output_boundary (q : Agent Empty) :
    Agent.Visible outWrapped (.output 9 wrapped) .nil ∧
    Agent.PayloadEvent.EquivE (.output 9 wrapped) (.output 9 (.const .one)) ∧
    ¬ Agent.Visible outOne (.output 9 wrapped) q := by
  refine ⟨.of_core (.output _ _ _),.output 9 (.equation (.fst _ _)),?_⟩
  intro h
  obtain ⟨body,hm⟩ := h.output_prefix
  simp [outOne,wrapped,Agent.threads,Agent.threadList] at hm

theorem exact_input_message_retained :
    ∃ q, Agent.Visible (.par .nil (.input 8 nestedReceiver)) (.input 8 wrapped) q ∧
      Agent.EvalEq (nestedReceiver.bind wrapped) q := by
  have he : Agent.EvalEq (.input 8 nestedReceiver) (.par .nil (.input 8 nestedReceiver)) :=
    .of_parEq ((Agent.ParEq.comm _ _).trans (.zero _)).symm
  exact he.input_transport (.of_core (.input 8 wrapped nestedReceiver)) (.refl _)

/-- Alias really chooses the value of an old free variable. -/
theorem let_uses_outer_environment :
    (letTerm (.var (7 : Nat)) (.output 9 (.var none) .nil)).Realizes
      (fun _ => .const .one) outOne := by
  refine ⟨.const .one,.nil,outOne,⟨.refl _,.refl _⟩,.refl _,?_⟩
  exact .of_parEq ((Agent.ParEq.comm _ _).trans (.zero _))

theorem unsatisfied_active_constraint_rejected (p : Agent Empty) :
    ¬ (active (0 : Nat) (.const .one)).Realizes (fun _ => .const .zero) p :=
  fun h => zero_not_one h.1

/-- The retained syntactically open Rewrite example still has its intended
interpretation for every value of the discarded, undefined variable. -/
theorem open_rewrite_interpretation (env : Fin 2 → Ground) (h : env 0 = .name 40) :
    SourceWellFormedSPOT.openAlias.Realizes env .nil ∧ ¬ SourceWellFormedSPOT.openAlias.Closed := by
  refine ⟨(SourceWellFormedSPOT.raw_rewrite_closedness_counterexample.2.1.realizes env .nil).mp ?_,
    SourceWellFormedSPOT.raw_rewrite_closedness_counterexample.2.2⟩
  exact ⟨h ▸ EqE.refl _,.refl _⟩

abbrev privatePair : Agent Empty :=
  .par (.output 8 wrapped .nil) (.input 8 (.output 9 (.var none) .nil))
abbrev privateResult : Agent Empty := .par .nil outWrapped

/-- This converse starts from the derived source reduction, with its actual
retained frame, and demands one real Tau plus complete handle preservation. -/
theorem actual_frame_private_reduction :
    (∀ i, EqE (SourceAtomicOutputSPOT.oldFrame.value i) (SourceAtomicOutputSPOT.oldFrame.value i)) ∧
    ∃ r, Agent.Tau privatePair r ∧ Agent.EvalEq privateResult r := by
  apply frameProcess_reduction_values SourceAtomicOutputSPOT.oldFrame SourceAtomicOutputSPOT.oldFrame
  apply Reduction.parRight
  exact tau_ground_derivable _ (Agent.Tau.of_core (.comm _ _ _ _))

/-- A canonical endpoint cannot hide a changed full frame behind the same body. -/
theorem canonical_frame_change_rejected (p q : Agent Empty) :
    ¬ Reduction (frameProcess (⟨fun _ => .const .zero⟩ : Frame ∅ 1) p)
      (frameProcess (⟨fun _ => .const .one⟩ : Frame ∅ 1) q) := by
  intro h
  have hv := (frameProcess_reduction_values _ _ p q h).1 0
  exact zero_not_one hv

end ExplainableCrypto.Helios.Symbolic.SourceInterpretationSPOT
