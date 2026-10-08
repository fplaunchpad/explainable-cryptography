import ExplainableCrypto.Helios.Symbolic.SourceParallelGuards
import ExplainableCrypto.Helios.Symbolic.SourceElectionSilent
import ExplainableCrypto.Helios.Symbolic.SourceElectionSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceParallelSPOT
open Historical General Source
abbrev ch := Channels.canonical
abbrev names := SharedTallySPOT.names
abbrev left := SharedTallySPOT.left
abbrev right := SharedTallySPOT.right
abbrev out40 : Agent Empty := .output 0 (.name 40) .nil
abbrev out41 : Agent Empty := .output 0 (.name 41) .nil
abbrev receiver : Agent (Option Empty) := .output 0 (.var none) .nil

/-- Parallel reassociation and null removal retain both distinct outputs. -/
theorem parallel_reordering : Agent.ParEq
    (.par .nil (.par out40 (.par out41 .nil))) (.par out41 out40) := by
  apply (Agent.parEq_iff_threads _ _).mpr
  simp only [Agent.threads_par,Agent.threads_nil,zero_add,add_comm]

/-- Replacing a multiset by a set would erase the second identical output. -/
theorem duplicate_thread_not_erased : ¬ Agent.ParEq (.par out40 out40) out40 := by
  intro h
  have hc := congrArg Multiset.card h.threads_eq
  simp [Agent.threads,Agent.threadList] at hc

/-- Parallel commutation does not commute two outputs in one continuation. -/
theorem sequential_outputs_not_reordered :
    ¬ Agent.ParEq (.output 0 (.name 40) out41) (.output 0 (.name 41) out40) := by
  intro h
  have he := h.threads_eq
  simp [Agent.threads,Agent.threadList] at he

/-- An internal redex below an output cannot run before that output. -/
theorem hidden_communication_cannot_run (q : Agent Empty) :
    ¬ Agent.Tau (.output 0 (.name 99) (.par (.output 8 (.name 40) .nil) (.input 8 receiver))) q :=
  Agent.tau_output_no_step _ _ _ _

/-- Even arbitrary parallel restructuring cannot make different channels match. -/
theorem wrong_channel_still_blocked (q : Agent Empty) :
    ¬ Agent.Tau (.par (.output 8 (.name 40) .nil) (.input 10 receiver)) q := by
  intro h
  rcases h.enabled with ⟨f,a,b,hm⟩ | ⟨c,m,a,b,ho,hi⟩
  · simp [Agent.threads,Agent.threadList] at hm
  · simp [Agent.threads,Agent.threadList] at ho hi
    omega

/-- The actual four-component election moves its first honest message into
the board and retains the second voter, first public relay and trustee. -/
theorem whole_election_first_handshake (swap : Bool) (extra : Nat) :
    Agent.Tau (electionBody names swap left right extra ch)
      (residual names swap left right extra ch .firstReceived) :=
  residual_receiveFirst names swap left right extra ch

/-- The second private receive is likewise a step of the entire residual. -/
theorem whole_election_second_handshake (swap : Bool) (extra : Nat) :
    Agent.Tau (residual names swap left right extra ch .firstPublished)
      (residual names swap left right extra ch .secondReceived) :=
  residual_receiveSecond names swap left right extra ch

/-- Both private tally exchanges run in their actual consecutive layouts,
including the reply orientation that required source parallel commutation. -/
theorem consecutive_private_handshakes (swap : Bool) :
    Relation.ReflTransGen Agent.Tau
      (residual names swap left right 2 ch (.sendTally [SharedTallySPOT.first,SharedTallySPOT.second]))
      (residual names swap left right 2 ch (.partialReady [SharedTallySPOT.first,SharedTallySPOT.second])) :=
  (Relation.ReflTransGen.single (residual_sendTally names swap left right 2 ch _)).tail
    (residual_receivePartial names swap left right 2 ch _)

/-- Rejection does not erase the waiting trustee. It nevertheless has no
internal step; proving no public input action additionally needs restriction. -/
theorem rejected_trustee_retained (swap : Bool) (rs : List (Recipe 3)) :
    residual names swap left right 2 ch (.rejected rs) ≠ .nil ∧
    ∀ q, ¬ Agent.Tau (residual names swap left right 2 ch (.rejected rs)) q := by
  refine ⟨?_,?_⟩
  · intro h
    cases h
  · intro q
    exact Agent.tau_input_no_step _ _ q

/-- A completed process is null and cannot acquire a tau step by restructuring. -/
theorem completed_residual_is_quiet (swap : Bool) (rs : List (Recipe 3)) :
    residual names swap left right 2 ch (.done rs) = .nil ∧
    ∀ q, ¬ Agent.Tau (residual names swap left right 2 ch (.done rs)) q :=
  ⟨rfl,Agent.tau_nil_no_step⟩
end ExplainableCrypto.Helios.Symbolic.SourceParallelSPOT
