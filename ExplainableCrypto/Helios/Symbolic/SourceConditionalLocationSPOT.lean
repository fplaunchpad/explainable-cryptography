import ExplainableCrypto.Helios.Symbolic.SourceNamedQuietPhases
import ExplainableCrypto.Helios.Symbolic.SourceCommunicationSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceConditionalLocationSPOT
open Historical General Source
abbrev ns := SharedTallySPOT.names
abbrev left := SharedTallySPOT.left
abbrev right := SharedTallySPOT.right
abbrev ch := Channels.canonical
abbrev test : Agent Empty := .branch (.equal (.const .zero) (.const .one)) (.output 9 (.name 40) .nil) .nil

theorem false_guard_is_ready : test.HasConditional := trivial

theorem readiness_does_not_prove_guard :
    test.HasConditional ∧ ¬ (Formula.equal (.const .zero) (.const .one) : Formula Empty).Holds Empty.elim :=
  ⟨trivial,zero_not_one⟩

theorem input_blocks_conditional :
    ¬ (Agent.input 8 (test.subst Empty.elim) : Agent Empty).HasConditional := id

theorem output_blocks_conditional :
    ¬ (Agent.output 8 (.name 40) test).HasConditional := id

theorem parallel_context_keeps_ready_conditional :
    (Agent.par (.input 8 .nil) (.par test (.output 9 (.name 41) .nil))).HasConditional :=
  .inr (.inl trivial)

theorem arbitrary_maps_do_not_expose_input (f g : Nat → Nat) :
    ¬ ((Agent.input 8 (test.subst Empty.elim) : Agent Empty).mapNames f g).HasConditional := id

theorem evaluated_equivalence_cannot_expose_output (p : Agent Empty)
    (h : Agent.EvalEq (.output 8 (.name 40) test) p) : ¬ p.HasConditional :=
  fun hp => h.hasConditional.mpr hp

theorem successful_private_conditional_is_actual :
    Named.Reduction
      (.newName (.base 40) (.embed (.plain (.branch SourceProcessSPOT.numericGuard (.output 9 SourceCommunicationSPOT.message .nil) .nil))))
      (.newName (.base 40) (.embed (.plain (.output 9 SourceCommunicationSPOT.message .nil)))) :=
  (.newName _ (.embed SourceCommunicationSPOT.successful_guard_has_its_own_classification) :
    Named.InternalStep (.conditional true) _ _).reduction

theorem every_check_is_ready (swap : Bool) (extra : Nat) (rs : List (Recipe 3)) (r : Recipe 3) :
    (residual ns swap left right extra ch (.check rs r)).HasConditional :=
  (residual_hasConditional_iff ns swap left right extra ch _).mpr ⟨rs,r,rfl⟩

theorem check_cannot_satisfy_noncheck_premise (rs : List (Recipe 3)) (r : Recipe 3) :
    ¬ (∀ xs x, (Process.Phase.check rs r) ≠ .check xs x) :=
  fun h => h rs r rfl

theorem exhausted_input_still_has_no_ready_conditional (swap : Bool) :
    ¬ (residual ns swap left right 0 ch (.input [])).HasConditional := by
  rw [residual_hasConditional_iff]
  simp

theorem arbitrary_first_step_is_communication (swap : Bool) (b : Named (Fin 1))
    (h : Named.Reduction
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right 0 ch .start)) b) :
    Named.InternalStep .communication
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right 0 ch .start)) b :=
  source_reduction_communication_of_not_check ns swap left right 0 ch .start
    (Named.restrictedState_interprets _) (by intros; simp) h

theorem actual_first_step_exists (swap : Bool) :
    Named.Reduction
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right 0 ch .start))
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right 0 ch .firstReceived)) :=
  (SourceCommunicationSPOT.actual_first_voter_has_communication_kind swap).reduction

theorem rejected_source_has_no_internal_target (swap : Bool) (b : Named (Fin 3)) :
    ¬ Named.Reduction
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right 1 ch (.rejected []))) b :=
  named_rejected_no_reduction ns swap left right 1 ch [] (.refl _)

theorem source_first_publication_cannot_be_skipped (swap : Bool) (b : Named (Fin 1)) :
    ¬ Named.Reduction
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right 0 ch .firstReceived)) b :=
  named_firstReceived_no_reduction ns swap left right 0 ch Channels.canonical_fresh (.refl _)

theorem source_input_cannot_be_skipped (swap : Bool) (b : Named (Fin 3)) :
    ¬ Named.Reduction
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right 1 ch (.input []))) b :=
  named_input_no_reduction ns swap left right 1 ch [] (by decide) (.refl _)

theorem completed_source_has_no_internal_target (swap : Bool) (b : Named (Fin 5)) :
    ¬ Named.Reduction
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right 0 ch (.done []))) b :=
  named_done_no_reduction ns swap left right 0 ch [] (.refl _)

theorem actual_accepted_and_rejected_source_checks (swap : Bool) :
    Named.Reduction
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right 1 ch (.check [] SharedTallySPOT.first)))
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right 1 ch (.sendTally [SharedTallySPOT.first]))) ∧
    Named.Reduction
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right 1 ch (.check [] (.var 1))))
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right 1 ch (.rejected []))) := by
  obtain ⟨ha,hr⟩ := SourceInternalSPOT.accepted_and_rejected_checks_exist swap
  exact ⟨Named.restricted_tau_derivable _ _ (.tau _ ha),Named.restricted_tau_derivable _ _ (.tau _ hr)⟩

theorem actual_noncheck_reduction_matches_in_either_world (swap swap' : Bool) :
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
  reachable_source_noncheck_internal_matching _ NumericReflectionSPOT.fixture_names_fresh swap swap'
    _ _ 0 Channels.canonical Channels.canonical_fresh .start .refl (by intros; simp) (.refl _) (.refl _)
    (SourceCommunicationSPOT.actual_first_voter_has_communication_kind swap).reduction


end ExplainableCrypto.Helios.Symbolic.SourceConditionalLocationSPOT
