import ExplainableCrypto.Helios.Symbolic.SourceGuardedElection
import ExplainableCrypto.Helios.Symbolic.SourceElectionSPOT
import ExplainableCrypto.Helios.Symbolic.SourceBoardTallySPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceGuardedBoardSPOT
open Historical General Source

abbrev ch := Channels.canonical
abbrev key := SourceElectionSPOT.key
abbrev first := SourceElectionSPOT.honestFirst
abbrev second := SourceElectionSPOT.honestSecond
abbrev incoming := SourceElectionSPOT.incoming

private theorem accepted (swap : Bool) :
    (electionGuard 0 key [first swap,second swap] (incoming swap)).Holds Empty.elim := by
  apply (electionGuard_ground _ _ _ _).mpr
  exact (SharedTallySPOT.fresh_sequence_accepted swap).1

/-- Independent fixture: receive, local save, another receive, then the saved,
new and old values in three distinct positions. -/
abbrev localReceiver : GuardedProgram (Option Nat) :=
  .letTerm (.var none) (.input 12 (.output 13
    (.binary .pair (.var (some none))
      (.binary .pair (.var none) (.var (some (some (some 7)))))) (.plain .nil)))

theorem local_and_input_binders_stay_distinct :
    (localReceiver.subst (inputSubst (.name 40 : Term Nat))).inline =
      .input 12 (.output 13 (.binary .pair (.name 40)
        (.binary .pair (.var none) (.var (some 7)))) .nil) := rfl

theorem supplied_free_none_is_not_captured :
    (localReceiver.subst (extendEnv (fun v : Nat => Term.var (some v)) (.var none))).inline =
      .input 12 (.output 13 (.binary .pair (.var (some none))
        (.binary .pair (.var none) (.var (some (some 7))))) .nil) := rfl

theorem capture_mutant_differs :
    (localReceiver.subst (extendEnv (fun v : Nat => Term.var (some v)) (.var none))).inline ≠
      .input 12 (.output 13 (.binary .pair (.var none)
        (.binary .pair (.var none) (.var (some (some 7))))) .nil) := by
  intro h
  rw [supplied_free_none_is_not_captured] at h
  cases h

theorem actual_open_input_activates_let :
    Extended.FreeStep (GuardedProgram.input 8 localReceiver).expand (.input 8 (.name 40))
      (.newVar (.par (.active none (.name 40))
        (.plain (.input 12 (.output 13 (.binary .pair (.var (some none))
          (.binary .pair (.var none) (.var (some (some 7))))) .nil))))) :=
  GuardedProgram.receives 8 (.name 40) localReceiver

theorem communication_preserves_sender :
    Extended.Reduction
      (.par (.plain (.output 8 (.name 40) (.output 9 (.name 41) .nil)))
        (GuardedProgram.input 8 localReceiver).expand)
      (.par (.plain (.output 9 (.name 41) .nil))
        (localReceiver.subst (inputSubst (.name 40))).expand) :=
  GuardedProgram.communicates 8 (.name 40) (.output 9 (.name 41) .nil) localReceiver

abbrev afterGuard : GuardedProgram Empty :=
  .letTerm (.name 40) (.output 9 (.var none) (.plain .nil))
abbrev numeric : Formula Empty := .equal (.binary .add (.const .zero) (.const .one)) (.const .one)

theorem semantic_guard_exposes_definition :
    Extended.Reduction (GuardedProgram.branch numeric afterGuard (.plain .nil)).expand
      (.newVar (.par (.active none (.name 40)) (.plain (.output 9 (.var none) .nil)))) :=
  GuardedProgram.selects_then numeric afterGuard (.plain .nil) (.equation .zero_one)

theorem semantic_disequality_rejects :
    Extended.Reduction (GuardedProgram.branch
      (.unequal (.binary .add (.const .zero) (.const .one)) (.const .one))
      afterGuard (.plain .nil)).expand (.plain .nil) :=
  GuardedProgram.selects_else _ _ _ (fun h => h (.equation .zero_one))

theorem publication_captures_full_fourth_field :
    Extended.BoundOutput (GuardedProgram.output 0
      (.spk (.name 40) (.name 41) (.const .one) (.name 99)) afterGuard).expand 0
      (.par (.active none (.spk (.name 40) (.name 41) (.const .one) (.name 99)))
        (.newVar (.par (.active none (.name 40)) (.plain (.output 9 (.var none) .nil))))) :=
  GuardedProgram.publishes 0 _ afterGuard

theorem changed_fourth_field_differs :
    (Term.spk (.name 40) (.name 41) (.const .one) (.name 99) : Ground) ≠
      .spk (.name 40) (.name 41) (.const .one) (.name 98) := by decide

theorem zero_extra_preserves_both_honest_inputs :
    (guardedBoardStart 1 0 ch key).inline =
      .input 2 (.output 0 (.var none) (.input 3 (.output 0 (.var none)
        (boardRegisterFinish ch
          (candidateTuple (boardTally (n := 1) (.var (some none)) (.var none) []))
          (boardTally (n := 1) (.var (some none)) (.var none) []))))) := by
  simp only [guardedBoardStart,guardedBoardSecond,guardedCollectBallots,
    GuardedProgram.inline,GuardedProgram.ofProgram_inline,boardTallyProgram_value]
  rfl

theorem pending_input_has_no_core_reduction (swap : Bool) (remaining : Nat) (p : Agent Empty) :
    ¬ Agent.CoreStep
      (guardedCollectBallots 0 ch (remaining+1) key (first swap) (second swap) []).inline p :=
  Agent.input_no_coreStep _ _ p

theorem next_input_retains_guard (swap : Bool) :
    Extended.FreeStep
      (guardedCollectBallots 0 ch 1 key (first swap) (second swap) []).expand
      (.input 4 (incoming swap))
      (guardedBoardCheck 0 0 ch key (first swap) (second swap) [] (incoming swap)).expand :=
  guardedCollectBallots_receives 0 0 ch key (first swap) (second swap) (incoming swap) []

theorem fresh_last_acceptance_exposes_all_lets (swap : Bool) :
    Extended.Reduction
      (guardedBoardCheck 0 0 ch key (first swap) (second swap) [] (incoming swap)).expand
      (boardTallyProgram (n := 0) ch (first swap) (second swap) [incoming swap]).compile :=
  guardedBoardCheck_last_accepts 0 ch key (first swap) (second swap) (incoming swap) [] (accepted swap)

theorem fresh_last_acceptance_reaches_canonical (swap : Bool) :
    Extended.Reduction
      (guardedBoardCheck 0 0 ch key (first swap) (second swap) [] (incoming swap)).expand
      (.plain (boardFinish (n := 0) ch (first swap) (second swap) [incoming swap])) :=
  guardedBoardCheck_last_canonical 0 ch key (first swap) (second swap) (incoming swap) [] (accepted swap)

theorem replay_rejects_before_any_tally (swap : Bool) (remaining : Nat) :
    Extended.Reduction
      (guardedBoardCheck 0 remaining ch key (first swap) (second swap) [] (first swap)).expand
      (.plain .nil) ∧
    ¬ (electionGuard 0 key [first swap,second swap] (first swap)).Holds Empty.elim := by
  have hf : ¬ (electionGuard 0 key [first swap,second swap] (first swap)).Holds Empty.elim := by
    intro h
    exact accepted_excludes_replay 0 key (first swap) _ (by simp)
      ((electionGuard_ground _ _ _ _).mp h)
  exact ⟨guardedBoardCheck_rejects 0 remaining ch key (first swap) (second swap) (first swap) [] hf,hf⟩

theorem two_candidate_block_retained :
    (guardedCollectBallots 1 ch 0 key SourceBoardTallySPOT.first SourceBoardTallySPOT.second
      [SourceBoardTallySPOT.third]).expand =
      SourceBoardTallySPOT.program.compile := GuardedProgram.ofProgram_expand _

theorem two_candidate_complete_continuation :
    (guardedCollectBallots 1 ch 0 key SourceBoardTallySPOT.first SourceBoardTallySPOT.second
      [SourceBoardTallySPOT.third]).inline =
      .output 1 (Term.tuple [SourceBoardTallySPOT.raw₀,SourceBoardTallySPOT.raw₁]) (.input 1
        (.output 0 (.var none) (.output 0 (Term.tuple
          [.binary .dec ((Term.var none).project 0) (shiftTerm SourceBoardTallySPOT.raw₀),
           .binary .dec ((Term.var none).project 1) (shiftTerm SourceBoardTallySPOT.raw₁)]) .nil))) := by
  rw [guardedCollectBallots,GuardedProgram.ofProgram_inline]
  exact SourceBoardTallySPOT.complete_ordered_continuation

theorem whole_board_congruence_for_all_sizes (n extra : Nat) (k : Term Nat) :
    Agent.EquivE (guardedBoardStart n extra ch k).inline (boardStart n extra ch k) :=
  guardedBoardStart_inline_equivE n extra ch k

theorem whole_election_congruence (swap : Bool) (extra : Nat) :
    Agent.EquivE
      (guardedElectionBody LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right extra ch)
      (electionBody LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right extra ch) :=
  guardedElectionBody_equivE _ _ _ _ _ _

theorem whole_election_has_actual_first_communication (swap : Bool) (extra : Nat) :
    ∃ q, Agent.Tau
      (guardedElectionBody LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right extra ch) q ∧
      Agent.EvalEq
        (residual LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right extra ch .firstReceived) q :=
  guardedElectionBody_tau_reverse _ _ _ _ _ _ (residual_receiveFirst _ _ _ _ _ _)

end ExplainableCrypto.Helios.Symbolic.SourceGuardedBoardSPOT
