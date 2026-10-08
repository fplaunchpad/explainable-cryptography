import ExplainableCrypto.Helios.Symbolic.SourceInternalCorrespondence
import ExplainableCrypto.Helios.Symbolic.SourceParallelSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceInternalSPOT
open Historical General Source
abbrev ch := Channels.canonical
abbrev names := SharedTallySPOT.names
abbrev left := SharedTallySPOT.left
abbrev right := SharedTallySPOT.right
abbrev first := SharedTallySPOT.first

/-- The actual fixed allocation satisfies every source channel separation rule. -/
theorem canonical_channel_policy : ch.Fresh := Channels.canonical_fresh

/-- A private first handshake exists, and every source successor has exactly
the stage-prescribed residual up to parallel structure. -/
theorem first_handshake_exact (swap : Bool) (extra : Nat) :
    Agent.Tau (electionBody names swap left right extra ch)
      (residual names swap left right extra ch .firstReceived) ∧
    ∀ q, Agent.Tau (electionBody names swap left right extra ch) q →
      Agent.ParEq q (residual names swap left right extra ch .firstReceived) := by
  refine ⟨residual_receiveFirst names swap left right extra ch,?_⟩
  intro q h
  exact residual_tau_deterministic names swap left right extra ch canonical_channel_policy .start True.intro h
    (residual_receiveFirst names swap left right extra ch)

theorem first_public_relay_cannot_be_skipped (swap : Bool) (extra : Nat) (q : Agent Empty) :
    ¬ Agent.Tau (residual names swap left right extra ch .firstReceived) q :=
  residual_firstReceived_no_tau names swap left right extra ch canonical_channel_policy q

theorem second_public_relay_cannot_be_skipped (swap : Bool) (extra : Nat) (q : Agent Empty) :
    ¬ Agent.Tau (residual names swap left right extra ch .secondReceived) q :=
  residual_secondReceived_no_tau names swap left right extra ch canonical_channel_policy q

theorem pending_public_voter_is_quiet (swap : Bool) (q : Agent Empty) :
    ¬ Agent.Tau (residual names swap left right 1 ch (.input [])) q :=
  residual_input_no_tau names swap left right 1 ch [] (by decide) q

/-- A real accepted ballot's check has exactly the tally continuation containing
that ballot; arbitrary parallel rewrites cannot silently omit it. -/
theorem accepted_check_target_exact (swap : Bool) (q : Agent Empty)
    (h : Agent.Tau (residual names swap left right 1 ch (.check [] first)) q) :
    Agent.ParEq q (residual names swap left right 1 ch (.sendTally [first])) := by
  have ha := (SharedTallySPOT.fresh_sequence_accepted swap).1
  change Process.accepts names swap left right [] first at ha
  have hh := residual_tau_deterministic names swap left right 1 ch canonical_channel_policy
    (.check [] first) (by unfold Process.Phase.inRange; decide) h (residual_accept names swap left right 1 ch [] first ha)
  simpa [Process.afterAccepted] using hh

/-- Replayed honest ciphertexts select the retained waiting trustee, with no
alternative internal target that continues collecting voters. -/
theorem replay_check_target_exact (swap : Bool) (q : Agent Empty)
    (h : Agent.Tau (residual names swap left right 1 ch (.check [] (.var 1))) q) :
    Agent.ParEq q (trusteeAgent (n := 0) ch (.name names.secretKey)) := by
  have hn : ¬ Process.accepts names swap left right [] (.var 1) := by
    intro ha
    exact SharedTallySPOT.honest_replay_rejected swap ⟨ha,True.intro⟩
  exact residual_tau_deterministic names swap left right 1 ch canonical_channel_policy
    (.check [] (.var 1)) (by unfold Process.Phase.inRange; decide) h (residual_reject names swap left right 1 ch [] (.var 1) hn)

/-- The two preceding target classifications are nonvacuous: both the real
accepted check and a replayed honest ballot have their respective Tau steps. -/
theorem accepted_and_rejected_checks_exist (swap : Bool) :
    Agent.Tau (residual names swap left right 1 ch (.check [] first))
      (residual names swap left right 1 ch (.sendTally [first])) ∧
    Agent.Tau (residual names swap left right 1 ch (.check [] (.var 1)))
      (residual names swap left right 1 ch (.rejected [])) := by
  have ha := (SharedTallySPOT.fresh_sequence_accepted swap).1
  change Process.accepts names swap left right [] first at ha
  have hn : ¬ Process.accepts names swap left right [] (.var 1) := by
    intro h
    exact SharedTallySPOT.honest_replay_rejected swap ⟨h,True.intro⟩
  refine ⟨?_,residual_reject names swap left right 1 ch [] (.var 1) hn⟩
  simpa [Process.afterAccepted] using residual_accept names swap left right 1 ch [] first ha

/-- The first receive cannot discard all the other components along with its
completed voter. Its prescribed residual still contains three active threads. -/
theorem remaining_context_cannot_be_erased (swap : Bool) (extra : Nat) :
    ¬ Agent.Tau (electionBody names swap left right extra ch) .nil := by
  intro h
  have he := (first_handshake_exact swap extra).2 .nil h
  have hc := congrArg Multiset.card he.threads_eq
  simp [residual,trusteeAgent,Agent.threads,Agent.threadList] at hc

/-- Deliberately violate broadcast/trustee separation while retaining the voter
numbering. The board can silently send its public ballot to the trustee. -/
def collidingChannels : Channels := ⟨1,1,fun i => i+2⟩

theorem channel_collision_refutes_omitted_policy (swap : Bool) :
    ¬ collidingChannels.Fresh ∧
    (∃ q, Agent.Tau (residual names swap left right 1 collidingChannels .secondReceived) q) ∧
    ∀ next, ¬ Process.Step names swap left right 1 .secondReceived .tau next := by
  refine ⟨?_,?_,?_⟩
  · intro hc
    exact hc.broadcast_trustee rfl
  · let first := ballot names 0 (choice swap left right 0).value
    let second := ballot names 1 (choice swap left right 1).value
    let continuation := collectBallots 0 collidingChannels 1 (publicKey names) first second []
    let body : Agent (Option Empty) := .output 1 (trusteeBody (n := 0) (.name names.secretKey)) .nil
    refine ⟨.par continuation (body.bind second),Agent.Tau.of_core ?_⟩
    exact .comm 1 second continuation body
  · intro next h
    cases h

/-- Omitting inRange misclassifies an exhausted collection as a waiting input.
Its literal process sends a tally, but that stage form has no tau constructor. -/
theorem exhausted_input_refutes_omitted_range (swap : Bool) :
    ¬ (Process.Phase.input []).inRange 0 ∧
    (∃ q, Agent.Tau (residual names swap left right 0 ch (.input [])) q) ∧
    ∀ next, ¬ Process.Step names swap left right 0 (.input []) .tau next := by
  refine ⟨by unfold Process.Phase.inRange; decide,?_,?_⟩
  · exact ⟨_,residual_sendTally names swap left right 0 ch []⟩
  · intro next h
    cases h
end ExplainableCrypto.Helios.Symbolic.SourceInternalSPOT
