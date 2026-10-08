import ExplainableCrypto.Helios.Symbolic.SourceReachableElectionPhases
import ExplainableCrypto.Helios.Symbolic.SourceCoordinatedSPOT
import ExplainableCrypto.Helios.Symbolic.SourceStructuralOpeningSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceReachableElectionSPOT
open Historical General Source
abbrev ns := SharedTallySPOT.names
abbrev left := SharedTallySPOT.left
abbrev right := SharedTallySPOT.right
abbrev ch := Channels.canonical
noncomputable abbrev raw (swap : Bool) (phase : Process.Phase) :=
  Named.restrictedState ch.privateChannels (sourceState ns swap left right 1 ch phase)
noncomputable abbrev initial (swap : Bool) := scopedVoterElection ns swap left right 1 ch

private theorem left_fresh : NoncesFreshFor ns left.value := by unfold NoncesFreshFor; decide
private theorem right_fresh : NoncesFreshFor ns right.value := by unfold NoncesFreshFor; decide

private theorem publication_execution (swap : Bool) {p q : Process.Phase} {handle : Nat} {m : Ground}
    (h : Publication ns swap left right 1 p handle m q) : Named.Execution (raw swap p) (raw swap q) := by
  have hp := h.scoped ch Channels.canonical_fresh
  cases h <;>
    obtain ⟨m,ho,hs⟩ := Named.restricted_output_derivable _ _ _ hp.1
  all_goals
    rw [eq_of_heq hp.2] at hs
    exact (Named.Execution.bound ho).trans
      ((Named.Execution.reindex _ Extended.outputHandle).trans (.structural hs))

theorem actual_scoped_start (swap : Bool) : Named.Execution (initial swap) (raw swap .start) :=
  .structural (scopedVoterElection_normalizes ns NumericReflectionSPOT.fixture_names_fresh swap
    left right left_fresh right_fresh 1 ch)

theorem actual_two_publications (swap : Bool) : Named.Execution (initial swap) (raw swap (.input [])) := by
  have hfirst : Named.Reduction (raw swap .start) (raw swap .firstReceived) :=
    Named.restricted_tau_derivable _ _ (.tau _ (residual_receiveFirst ns swap left right 1 ch))
  have hsecond : Named.Reduction (raw swap .firstPublished) (raw swap .secondReceived) :=
    Named.restricted_tau_derivable _ _ (.tau _ (residual_receiveSecond ns swap left right 1 ch))
  exact (actual_scoped_start swap).trans ((Named.Execution.internal hfirst).trans
    ((publication_execution swap .first).trans ((Named.Execution.internal hsecond).trans
      (publication_execution swap .second))))

theorem actual_replay_input (swap : Bool) :
    Named.FreeStep (raw swap (.input [])) (.input 4 (.var (1 : Fin 3))) (raw swap (.check [] (.var (1 : Fin 3)))) :=
  Named.restricted_input_derivable _ _ _ _
    (.input _ _ _ (by decide) trivial (residual_visible_input ns swap left right 1 ch [] (.var (1 : Fin 3)) (by decide)))

theorem actual_replay_rejection (swap : Bool) :
    Named.Reduction (raw swap (.check [] (.var (1 : Fin 3)))) (raw swap (.rejected [])) :=
  Named.restricted_tau_derivable _ _ (.tau _
    (residual_reject ns swap left right 1 ch [] (.var (1 : Fin 3))
      (fun h => SharedTallySPOT.honest_replay_rejected swap ⟨h,True.intro⟩)))

theorem actual_mixed_execution_rejects (swap : Bool) :
    Named.Execution (initial swap) (raw swap (.rejected [])) :=
  (actual_two_publications swap).trans ((Named.Execution.free (actual_replay_input swap)).trans
    (.internal (actual_replay_rejection swap)))

theorem mixed_execution_has_reached_phase (swap : Bool) :
    ∃ (phase : Process.Phase) (e k : Nat ≃ Nat) (i : Fin 3 ≃ Fin phase.handles),
      Process.Reachable ns swap left right 1 phase ∧
      Named.JointOpening ((raw swap (.rejected [])).rename i)
        (Named.mappedState ch.privateChannels (sourceState ns swap left right 1 ch phase) e k) :=
  scopedVoterElection_execution_phase ns NumericReflectionSPOT.fixture_names_fresh swap left right
    left_fresh right_fresh 1 ch Channels.canonical_fresh (actual_mixed_execution_rejects swap)

abbrev exchange : Fin 3 ≃ Fin 3 := Equiv.swap 0 2

theorem reindexed_mixed_execution_has_reached_phase (swap : Bool) :
    ∃ (phase : Process.Phase) (e k : Nat ≃ Nat) (i : Fin 3 ≃ Fin phase.handles),
      Process.Reachable ns swap left right 1 phase ∧
      Named.JointOpening (((raw swap (.rejected [])).rename exchange).rename i)
        (Named.mappedState ch.privateChannels (sourceState ns swap left right 1 ch phase) e k) :=
  scopedVoterElection_execution_phase ns NumericReflectionSPOT.fixture_names_fresh swap left right
    left_fresh right_fresh 1 ch Channels.canonical_fresh
    ((actual_mixed_execution_rejects swap).trans (.reindex _ exchange))

theorem every_reached_raw_state_rejects_old_handle_output (swap : Bool) {V : Type} {a : Named V}
    (h : Named.Execution (initial swap) a) (c : Nat) (x : V) (b : Named V) :
    ¬ Named.FreeStep a (.output c x) b :=
  scopedVoterElection_execution_no_handle_output ns NumericReflectionSPOT.fixture_names_fresh swap
    left right left_fresh right_fresh 1 ch Channels.canonical_fresh h c x b

theorem replay_rejection_has_no_next_public_input (swap : Bool) (c : Nat) (r : Recipe 3)
    (b : Named (Fin 3)) : ¬ Named.FreeStep (raw swap (.rejected [])) (.input c r) b :=
  SourceNamedVisibleSPOT.rejected_election_has_no_named_input swap c r b

theorem handle_renaming_retains_full_input_and_target (swap : Bool) :
    Named.FreeStep ((raw swap (.input [])).rename exchange)
      ((Extended.FreeLabel.input 4 (.var (1 : Fin 3))).rename exchange)
      ((raw swap (.check [] (.var (1 : Fin 3)))).rename exchange) :=
  (actual_replay_input swap).rename_equiv exchange

theorem fresh_output_is_after_every_old_handle :
    ((Equiv.optionCongr (Equiv.swap (0 : Fin 2) 1)).trans Extended.outputHandle) none = 2 ∧
    ((Equiv.optionCongr (Equiv.swap (0 : Fin 2) 1)).trans Extended.outputHandle) (some 0) = 1 ∧
    ((Equiv.optionCongr (Equiv.swap (0 : Fin 2) 1)).trans Extended.outputHandle) (some 1) = 0 := by decide

theorem merging_fresh_and_old_handle_is_impossible :
    ¬ ((Equiv.optionCongr (Equiv.swap (0 : Fin 2) 1)).trans Extended.outputHandle) none =
      ((Equiv.optionCongr (Equiv.swap (0 : Fin 2) 1)).trans Extended.outputHandle) (some 0) := by decide

theorem semantic_only_reconstruction_remains_refuted :
    SourceLocalRigiditySPOT.cycle.SameRealizations SourceLocalRigiditySPOT.emptyState ∧
    ¬ Named.Structural (.embed SourceLocalRigiditySPOT.cycle) (.embed SourceLocalRigiditySPOT.emptyState) :=
  SourceStructuralOpeningSPOT.semantic_equality_is_insufficient

end ExplainableCrypto.Helios.Symbolic.SourceReachableElectionSPOT
