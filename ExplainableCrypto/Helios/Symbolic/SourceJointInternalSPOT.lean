import ExplainableCrypto.Helios.Symbolic.SourceElectionJointInvariant
import ExplainableCrypto.Helios.Symbolic.SourceJointOpeningSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceJointInternalSPOT
open Historical General Source SourceTargetInvariantSPOT

noncomputable abbrev wrappedAfter : Named (Fin 1) := .par rawAfter (.embed (.plain .nil))

theorem actual_raw_then_target : Named.Reduction rawBefore wrappedAfter :=
  .congr (.refl _) actual_named_then (Named.Structural.zero rawAfter).symm

theorem raw_then_target_retains_joint : Named.JointOpening wrappedAfter rawAfter :=
  (Named.restrictedState_jointOpening s).internal actual_raw_then_target then_target_is_deterministic

theorem raw_target_keeps_private_input (b : Named (Fin 1)) :
    ¬ Named.FreeStep wrappedAfter (.input 18 (.name 40)) b :=
  raw_then_target_retains_joint.private_free_blocked t _ (by decide)

theorem raw_target_keeps_private_output (b : Named (Option (Fin 1))) :
    ¬ Named.BoundOutput wrappedAfter 18 b :=
  raw_then_target_retains_joint.private_bound_blocked t 18 (by decide)

theorem full_target_interpretation_exists :
    ∃ env p, wrappedAfter.Interprets NameAssignment.literal env p ∧
      rawAfter.Interprets NameAssignment.literal env p := raw_then_target_retains_joint.interprets

theorem wrong_branch_joint_target_rejected :
    ¬ Named.JointOpening rawAfter (Named.restrictedState {18} (⟨φ,.par bad waiting⟩ : ScopedState {40} 1)) := by
  intro h
  have hc : 8 ∈ rawAfter.channels := (Named.channel_mem_restrictedState {18} t 8).mpr ⟨by decide,by decide⟩
  rw [h.channels] at hc
  have hm := ((Named.channel_mem_restrictedState {18} _ 8).mp hc).1
  exact (by decide : 8 ∉ (Agent.par bad waiting).channels) hm

theorem wrong_old_handle_rejected (q : Agent Empty) :
    ¬ (Extended.frameProcess φ after).Realizes (fun _ => .name 41) q :=
  target_excludes_wrong_handle_value q

theorem full_payload_and_waiting_input_retained :
    after = .par (.output 8 (.spk (.name 40) (.name 41) (.const .one) (.name 99)) .nil) (.input 18 .nil) := rfl

theorem else_branch_retains_joint : Named.JointOpening rawAfter rawAfter := by
  have h : Named.Reduction (Named.restrictedState {18} (⟨φ,falseBefore⟩ : ScopedState {40} 1)) rawAfter :=
    Named.restricted_tau_derivable _ _ (.tau φ actual_else_tau)
  exact (Named.restrictedState_jointOpening _).internal h else_target_is_deterministic

abbrev privateBefore : Agent Empty :=
  .par (.output 18 payload (.output 18 (.name 41) .nil)) (.input 18 (.output 8 (.var none) .nil))
abbrev privateAfter : Agent Empty := .par (.output 18 (.name 41) .nil) (.output 8 payload .nil)
abbrev privateSource : ScopedState {40} 1 := ⟨φ,privateBefore⟩
abbrev privateTarget : ScopedState {40} 1 := ⟨φ,privateAfter⟩

theorem actual_private_tau : Agent.Tau privateBefore privateAfter := .of_core (.comm 18 payload _ _)

theorem private_target_is_deterministic (q : Agent Empty) (h : Agent.Tau privateBefore q) :
    Agent.EvalEq q privateAfter := .of_parEq (Agent.tau_pair_deterministic h actual_private_tau)

theorem actual_private_named_communication :
    Named.Reduction (Named.restrictedState {18} privateSource) (Named.restrictedState {18} privateTarget) :=
  Named.restricted_tau_derivable privateSource privateTarget (.tau φ actual_private_tau)

theorem private_communication_retains_joint :
    Named.JointOpening (Named.restrictedState {18} privateTarget) (Named.restrictedState {18} privateTarget) :=
  (Named.restrictedState_jointOpening privateSource).internal actual_private_named_communication private_target_is_deterministic

theorem surviving_private_output_stays_blocked (b : Named (Option (Fin 1))) :
    ¬ Named.BoundOutput (Named.restrictedState {18} privateTarget) 18 b :=
  private_communication_retains_joint.private_bound_blocked privateTarget 18 (by decide)

theorem competing_internal_targets_refute_determinism :
    ¬ (∀ q, Agent.Tau racing q → Agent.EvalEq q branchFirst) := dropping_determinism_is_invalid

theorem full_body_does_not_replace_joint_policy :
    ¬ Named.JointOpening SourceVisibleInvariantSPOT.rawPublic
      (Named.restrictedState {8} SourceVisibleInvariantSPOT.canonical) :=
  SourceJointOpeningSPOT.private_public_pair_rejected

theorem two_internal_election_steps_retain_joint (swap : Bool) :
    ∃ next, Process.Reachable ens swap left right 0 next ∧
      Relation.ReflTransGen (fun p q => Process.Step ens swap left right 0 p .tau q) (.sendTally []) next ∧
      PhaseJointOpening ens swap left right 0 ch next (raw swap (.partialReady [])) :=
  PhaseJointOpening.canonical.internal_trace Channels.canonical_fresh (tally_phase_is_reached swap)
    (actual_two_internal_actions swap)

theorem every_raw_internal_trace_keeps_private_outputs_blocked (swap : Bool) {b : Named (Fin 3)}
    (h : Relation.ReflTransGen (@Named.Reduction (Fin 3)) (raw swap (.sendTally [])) b)
    (c : Nat) (hc : c ∈ ch.privateChannels) (d : Named (Option (Fin 3))) : ¬ Named.BoundOutput b c d := by
  obtain ⟨_,_,_,hb⟩ := PhaseJointOpening.canonical.internal_trace Channels.canonical_fresh
    (tally_phase_is_reached swap) h
  exact fun hd => hb.bound_channel_public hd hc

theorem every_raw_internal_trace_keeps_private_inputs_blocked (swap : Bool) {b : Named (Fin 3)}
    (h : Relation.ReflTransGen (@Named.Reduction (Fin 3)) (raw swap (.sendTally [])) b)
    (c : Nat) (hc : c ∈ ch.privateChannels) (r : Term (Fin 3)) (d : Named (Fin 3)) :
    ¬ Named.FreeStep b (.input c r) d := by
  obtain ⟨_,_,_,hb⟩ := PhaseJointOpening.canonical.internal_trace Channels.canonical_fresh
    (tally_phase_is_reached swap) h
  exact fun hd => hb.free_channel_public hd hc

end ExplainableCrypto.Helios.Symbolic.SourceJointInternalSPOT
