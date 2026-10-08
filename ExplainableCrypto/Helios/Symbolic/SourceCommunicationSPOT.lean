import ExplainableCrypto.Helios.Symbolic.SourceClassifiedElection
import ExplainableCrypto.Helios.Symbolic.SourceNamedVisibleSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceCommunicationSPOT
open Historical General Source

theorem communication_and_guard_kinds_differ :
    InternalKind.communication ≠ .conditional true ∧
      InternalKind.communication ≠ .conditional false ∧
      InternalKind.conditional true ≠ .conditional false := by decide

abbrev message : Ground := .spk (.name 40) (.name 41) (.const .one) (.name 99)
abbrev before : Agent Empty := .par (.output 8 message .nil) (.input 8 (.output 9 (.var none) .nil))
abbrev after : Agent Empty := .par .nil (.output 9 message .nil)
abbrev privateBefore : Named Empty := .newName (.base 40) (.newName (.channel 8) (.embed (.plain before)))
abbrev privateAfter : Named Empty := .newName (.base 40) (.newName (.channel 8) (.embed (.plain after)))

theorem full_message_communication_classified :
    Extended.InternalStep .communication (.plain before) (.plain after) :=
  .message_communication 8 message .nil (.output 9 (.var none) .nil)

theorem actual_private_communication : Named.InternalStep .communication privateBefore privateAfter :=
  .newName _ (.newName _ (.embed full_message_communication_classified))

theorem classified_communication_erases_to_actual_step : Named.Reduction privateBefore privateAfter :=
  actual_private_communication.reduction

theorem actual_reduction_has_a_classification :
    ∃ kind, Named.InternalStep kind privateBefore privateAfter :=
  classified_communication_erases_to_actual_step.classify

theorem private_communication_keeps_full_interpretation :
    ∃ q, Agent.Tau before q ∧ privateAfter.Interprets NameAssignment.literal Empty.elim q :=
  actual_private_communication.communication_interprets NameAssignment.literal Empty.elim
    ⟨40,8,.refl _⟩

theorem expected_complete_continuation :
    privateAfter.Interprets NameAssignment.literal Empty.elim after ∧
      message = .spk (.name 40) (.name 41) (.const .one) (.name 99) :=
  ⟨⟨40,8,.refl _⟩,rfl⟩

abbrev collapsedChannels : NameAssignment
  | .base n => n
  | .channel _ => 0

theorem forward_communication_allows_colliding_channels :
    ∃ q, Agent.Tau (.par (.output 0 message .nil) (.input 0 (.output 0 (.var none) .nil))) q ∧
      privateAfter.Interprets collapsedChannels Empty.elim q :=
  actual_private_communication.communication_interprets collapsedChannels Empty.elim ⟨40,0,.refl _⟩

theorem channel_collapse_is_not_faithful :
    ¬ collapsedChannels.FaithfulOn {SourceName.channel 8,SourceName.channel 9} := by
  intro h
  have he := h (a := .channel 8) (b := .channel 9) (by simp) (by simp) rfl
  cases he

theorem distinct_channels_cannot_communicate (b : Named Empty) :
    ¬ Named.InternalStep .communication
      (.embed (.plain (.par (.output 8 message .nil) (.input 10 (.output 9 (.var none) .nil))))) b := by
  intro h
  obtain ⟨q,hq,_⟩ := h.communication_interprets NameAssignment.literal Empty.elim (.refl _)
  exact Agent.tau_output_input_no_step (by decide : (8 : Nat) ≠ 10) hq

theorem collapse_can_create_a_new_core_communication :
    Agent.CoreStep (SourceNamedBodySPOT.wrongChannels.mapNames id (fun _ => 0))
      (.par .nil (.output 0 (.name 40) .nil)) :=
  SourceNamedBodySPOT.collapsing_channels_creates_communication

theorem successful_guard_has_its_own_classification :
    Extended.InternalStep (.conditional true)
      (.plain (.branch SourceProcessSPOT.numericGuard (.output 9 message .nil) .nil))
      (.plain (.output 9 message .nil)) :=
  .thenBranch SourceProcessSPOT.numericGuard _ _ (EqE.equation .zero_one)

theorem failed_guard_has_its_own_classification :
    Extended.InternalStep (.conditional false)
      (.plain (.branch (.equal (.const .zero) (.const .one)) (.output 9 message .nil) .nil : Agent Empty))
      (.plain .nil) :=
  .elseBranch (.equal (.const .zero) (.const .one)) _ _ zero_not_one

theorem failed_guard_is_still_an_actual_reduction :
    Extended.Reduction
      (.plain (.branch (.equal (.const .zero) (.const .one)) (.output 9 message .nil) .nil : Agent Empty))
      (.plain .nil) := failed_guard_has_its_own_classification.reduction

theorem empty_process_has_no_classified_step (kind : InternalKind) (b : Extended Empty) :
    ¬ Extended.InternalStep kind (.plain .nil) b := by
  intro h
  obtain ⟨q,hq,_⟩ := h.reduction.realizes Empty.elim (p := .nil) (.refl _)
  exact Agent.tau_nil_no_step q hq

theorem guard_collision_remains_an_obstruction :
    SourceNamedBodySPOT.distinctGuard.Holds Empty.elim ∧
      ¬ (SourceNamedBodySPOT.distinctGuard.mapNames (fun _ => 0)).Holds Empty.elim :=
  SourceNamedVisibleSPOT.guard_collision_still_changes_branch

theorem actual_first_voter_has_communication_kind (swap : Bool) :
    Named.InternalStep .communication
      (Named.restrictedState Channels.canonical.privateChannels
        (sourceState SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 0 Channels.canonical .start))
      (Named.restrictedState Channels.canonical.privateChannels
        (sourceState SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 0 Channels.canonical .firstReceived)) :=
  named_receiveFirst_classified _ _ _ _ _ _

theorem actual_trustee_keeps_tally_and_reply (swap : Bool) :
    Named.InternalStep .communication
      (Named.restrictedState Channels.canonical.privateChannels
        (sourceState SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 0 Channels.canonical (.sendTally [])))
      (Named.restrictedState Channels.canonical.privateChannels
        (sourceState SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 0 Channels.canonical (.trusteeReply []))) :=
  named_sendTally_classified _ _ _ _ _ _ _

theorem first_voter_matches_in_either_world (swap swap' : Bool) :
    ∃ (next : Process.Phase) (q : ScopedState SharedTallySPOT.names.restricted 1),
      Process.Reachable SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 0 next ∧
      Named.Reduction
        (Named.restrictedState Channels.canonical.privateChannels
          (sourceState SharedTallySPOT.names swap' SharedTallySPOT.left SharedTallySPOT.right 0 Channels.canonical .start))
        (Named.restrictedState Channels.canonical.privateChannels q) ∧
      q.frame = sourceView SharedTallySPOT.names swap' SharedTallySPOT.left SharedTallySPOT.right .start ∧
      q.body = residual SharedTallySPOT.names swap' SharedTallySPOT.left SharedTallySPOT.right 0 Channels.canonical next ∧
      (Named.restrictedState Channels.canonical.privateChannels
        (sourceState SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 0 Channels.canonical .firstReceived)).Interprets NameAssignment.literal
          (sourceView SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right .start).value
          (residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 0 Channels.canonical next) ∧
      Named.StaticEq
        (Named.restrictedState Channels.canonical.privateChannels
          (sourceState SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 0 Channels.canonical .firstReceived))
        (Named.restrictedState Channels.canonical.privateChannels q) :=
  reachable_source_communication_matching _ NumericReflectionSPOT.fixture_names_fresh swap swap'
    _ _ 0 Channels.canonical Channels.canonical_fresh .start .refl (.refl _) (.refl _)
    (actual_first_voter_has_communication_kind swap)

theorem rejected_election_has_no_communication (swap : Bool) (b : Named (Fin 3)) :
    ¬ Named.InternalStep .communication
      (Named.restrictedState Channels.canonical.privateChannels
        (sourceState SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical (.rejected []))) b := by
  intro h
  obtain ⟨q,hq,_⟩ := h.communication_interprets NameAssignment.literal _
    (Named.restrictedState_interprets _)
  exact residual_rejected_no_tau SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right
    1 Channels.canonical [] q hq

theorem arbitrary_source_step_retains_conditional_alternative (a b : Named (Fin 1))
    (p : Agent Empty) (h : Named.Reduction a b)
    (ha : a.Interprets NameAssignment.literal (fun _ => .name 40) p) :
    (∃ q, Agent.Tau p q ∧ b.Interprets NameAssignment.literal (fun _ => .name 40) q) ∨
      ∃ taken, Named.InternalStep (.conditional taken) a b :=
  h.interprets_or_conditional NameAssignment.literal _ ha

end ExplainableCrypto.Helios.Symbolic.SourceCommunicationSPOT
