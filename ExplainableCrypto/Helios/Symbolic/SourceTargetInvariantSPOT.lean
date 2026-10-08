import ExplainableCrypto.Helios.Symbolic.SourceOpeningInternalTraces
import ExplainableCrypto.Helios.Symbolic.SourceOpeningComparisonSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceTargetInvariantSPOT
open Historical General Source

abbrev φ : Frame {40} 1 := ⟨fun _ => .name 40⟩
abbrev guard : Formula Empty := .equal (.name 40) (.name 40)
abbrev payload : Ground := .spk (.name 40) (.name 41) (.const .one) (.name 99)
abbrev good : Agent Empty := .output 8 payload .nil
abbrev bad : Agent Empty := .branch guard .nil .nil
abbrev waiting : Agent Empty := .input 18 .nil
abbrev before : Agent Empty := .par (.branch guard good bad) waiting
abbrev after : Agent Empty := .par good waiting

theorem actual_then_tau : Agent.Tau before after :=
  (Agent.Tau.of_core (.thenBranch guard good bad (.refl _))).parLeft waiting

theorem then_target_is_deterministic (q : Agent Empty) (h : Agent.Tau before q) :
    Agent.EvalEq q after := .of_parEq (Agent.tau_branch_input_deterministic h actual_then_tau)

theorem full_frame_actual_reduction :
    Extended.Reduction (Extended.frameProcess φ before) (Extended.frameProcess φ after) :=
  .parRight _ (Extended.tau_ground_derivable (Fin 1) actual_then_tau)

theorem target_has_backward_full_realization :
    ∃ p r, (Extended.frameProcess φ before).Realizes φ.value p ∧ Agent.Tau p r ∧ Agent.EvalEq r after :=
  full_frame_actual_reduction.realizes_backward φ.value (Extended.frameProcess_realizes φ after)

theorem every_environment_is_preserved (env : Fin 1 → Ground) :
    (∃ p, (Extended.frameProcess φ before).Realizes env p) ↔
      ∃ q, (Extended.frameProcess φ after).Realizes env q :=
  full_frame_actual_reduction.has_realization_iff env

theorem deterministic_full_target_class :
    (Extended.frameProcess φ after).SameRealizations (Extended.frameProcess φ after) :=
  full_frame_actual_reduction.sameRealizations_frame_target φ before after (.refl _) then_target_is_deterministic

theorem target_excludes_wrong_handle_value (q : Agent Empty) :
    ¬ (Extended.frameProcess φ after).Realizes (fun _ => .name 41) q := by
  intro h
  have hv := ((Extended.frameProcess_realizes_iff φ after _ q).mp h).1 0
  have he := (EqE.name_iff 41 40).mp hv
  cases he

theorem whole_payload_and_waiting_input_survive :
    after = .par (.output 8 (.spk (.name 40) (.name 41) (.const .one) (.name 99)) .nil) (.input 18 .nil) := rfl

theorem wrong_branch_is_not_a_target_realization :
    ¬ (Extended.frameProcess φ after).Realizes φ.value (.par bad waiting) := by
  intro h
  have he := ((Extended.frameProcess_realizes_iff φ after _ _).mp h).2.hasConditional
  simp [Agent.HasConditional] at he

abbrev s : ScopedState {40} 1 := ⟨φ,before⟩
abbrev t : ScopedState {40} 1 := ⟨φ,after⟩
noncomputable abbrev rawBefore := Named.restrictedState {18} s
noncomputable abbrev rawAfter := Named.restrictedState {18} t

theorem canonical_source_has_full_invariant : Named.HasCanonicalOpening rawBefore φ before :=
  Named.restrictedState_hasCanonicalOpening s

theorem actual_named_then : Named.Reduction rawBefore rawAfter :=
  Named.restricted_tau_derivable s t (.tau φ actual_then_tau)

theorem internal_action_retains_full_invariant : Named.HasCanonicalOpening rawAfter φ after :=
  canonical_source_has_full_invariant.internal actual_named_then then_target_is_deterministic

theorem target_can_be_refreshed_again (avoid : Finset SourceName) :
    ∃ (ns : List SourceName) (b : Extended (Fin 1)) (e k : Nat ≃ Nat),
      Named.Opens rawAfter NameAssignment.literal ns b ∧
      (∀ n ∈ ns, n ∉ avoid ∪ rawAfter.freeNames) ∧
      b.SameRealizations ((Extended.frameProcess φ after).mapNames e k) :=
  internal_action_retains_full_invariant.fresh avoid

theorem invariant_supplies_a_nonvacuous_full_interpretation :
    ∃ e k : Nat ≃ Nat,
      rawAfter.Interprets NameAssignment.literal (φ.mapNames e).value (after.mapNames e k) :=
  internal_action_retains_full_invariant.interprets

theorem captured_allocation_fails_refresh_premise :
    SourceName.base 41 ∈ SourceOpeningSPOT.guarded.freeNames := by decide

abbrev falseGuard : Formula Empty := .unequal (.name 40) (.name 40)
abbrev falseBefore : Agent Empty := .par (.branch falseGuard bad good) waiting

theorem actual_else_tau : Agent.Tau falseBefore after :=
  (Agent.Tau.of_core (.elseBranch falseGuard bad good (fun h => h (.refl _)))).parLeft waiting

theorem else_target_is_deterministic (q : Agent Empty) (h : Agent.Tau falseBefore q) :
    Agent.EvalEq q after := .of_parEq (Agent.tau_branch_input_deterministic h actual_else_tau)

theorem actual_else_retains_full_invariant :
    Named.HasCanonicalOpening rawAfter φ after := by
  have h : Named.Reduction (Named.restrictedState {18} (⟨φ,falseBefore⟩ : ScopedState {40} 1)) rawAfter :=
    Named.restricted_tau_derivable _ _ (.tau φ actual_else_tau)
  exact (Named.restrictedState_hasCanonicalOpening _).internal h else_target_is_deterministic

abbrev handshake : Agent Empty := .par (.output 8 (.name 40) .nil) (.input 8 .nil)
abbrev racing : Agent Empty := .par bad handshake
abbrev branchFirst : Agent Empty := .par .nil handshake
abbrev commFirst : Agent Empty := .par bad (.par .nil .nil)

theorem competing_branch_is_actual : Agent.Tau racing branchFirst :=
  (Agent.Tau.of_core (.thenBranch guard .nil .nil (.refl _))).parLeft handshake

theorem competing_communication_is_actual : Agent.Tau racing commFirst :=
  (Agent.Tau.of_core (.comm 8 (.name 40) .nil .nil)).parRight bad

theorem competing_outcomes_are_distinct : ¬ Agent.EvalEq branchFirst commFirst := by
  intro h
  have he := h.hasConditional
  simp [Agent.HasConditional] at he

theorem dropping_determinism_is_invalid :
    ¬ (∀ q, Agent.Tau racing q → Agent.EvalEq q branchFirst) := by
  intro h
  exact competing_outcomes_are_distinct (h commFirst competing_communication_is_actual).symm

abbrev ens := SharedTallySPOT.names
abbrev left := SharedTallySPOT.left
abbrev right := SharedTallySPOT.right
abbrev ch := Channels.canonical
abbrev es (swap : Bool) (p : Process.Phase) := sourceState ens swap left right 0 ch p
noncomputable abbrev raw (swap : Bool) (p : Process.Phase) := Named.restrictedState ch.privateChannels (es swap p)

theorem tally_phase_is_reached (swap : Bool) : Process.Reachable ens swap left right 0 (.sendTally []) := by
  have h : Process.Reachable ens swap left right 0 (Process.afterAccepted 0 []) :=
    (((Relation.ReflTransGen.refl.tail ⟨.tau,Process.Step.receiveFirst⟩).tail
      ⟨.output 1,Process.Step.publishFirst⟩).tail ⟨.tau,Process.Step.receiveSecond⟩).tail
      ⟨.output 2,Process.Step.publishSecond⟩
  simpa only [Process.afterAccepted,List.length_nil,lt_self_iff_false,if_false] using h

theorem actual_two_internal_actions (swap : Bool) :
    Relation.ReflTransGen (@Named.Reduction (Fin 3)) (raw swap (.sendTally [])) (raw swap (.partialReady [])) := by
  have h₁ := Named.restricted_tau_derivable (hidden := ch.privateChannels) (es swap (.sendTally [])) (es swap (.trusteeReply []))
    (.tau _ (residual_tau_step ens swap left right 0 ch Process.Step.sendTally))
  have h₂ := Named.restricted_tau_derivable (hidden := ch.privateChannels) (es swap (.trusteeReply [])) (es swap (.partialReady []))
    (.tau _ (residual_tau_step ens swap left right 0 ch Process.Step.receivePartial))
  exact (Relation.ReflTransGen.refl.tail h₁).tail h₂

theorem actual_two_step_trace_preserves_invariant (swap : Bool) :
    ∃ next, Process.Reachable ens swap left right 0 next ∧
      Relation.ReflTransGen (fun p q => Process.Step ens swap left right 0 p .tau q) (.sendTally []) next ∧
      PhaseOpening ens swap left right 0 ch next (raw swap (.partialReady [])) :=
  PhaseOpening.canonical.internal_trace Channels.canonical_fresh (tally_phase_is_reached swap)
    (actual_two_internal_actions swap)

theorem trustee_internal_frame_is_literal (swap : Bool) :
    HEq (sourceView ens swap left right (.sendTally [])) (sourceView ens swap left right (.trusteeReply [])) :=
  (Process.Step.sendTally (ns := ens) (swap := swap) (left := left) (right := right) (extra := 0)).tau_sourceView

theorem public_publication_changes_handle_domain :
    (Process.Phase.partialReady []).handles ≠ (Process.Phase.resultReady []).handles := by decide

end ExplainableCrypto.Helios.Symbolic.SourceTargetInvariantSPOT
