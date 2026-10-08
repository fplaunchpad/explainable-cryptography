import ExplainableCrypto.Helios.Symbolic.SourceElectionHandleExclusion
import ExplainableCrypto.Helios.Symbolic.SourceHandleOutputDerivation
import ExplainableCrypto.Helios.Symbolic.SourceCoordinatedSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceElectionHandleSPOT
open Historical General Source
abbrev ns := SharedTallySPOT.names
abbrev left := SharedTallySPOT.left
abbrev right := SharedTallySPOT.right
abbrev ch := Channels.canonical
abbrev e := SourceCoordinatedSPOT.e
abbrev k := SourceCoordinatedSPOT.k
abbrev es (swap : Bool) (phase : Process.Phase) := sourceState ns swap left right 0 ch phase
noncomputable abbrev raw (swap : Bool) (phase : Process.Phase) := Named.mappedState ch.privateChannels (es swap phase) e k

private theorem first_reached (swap : Bool) : Process.Reachable ns swap left right 0 .firstReceived :=
  .tail .refl ⟨.tau,.receiveFirst⟩
private theorem second_reached (swap : Bool) : Process.Reachable ns swap left right 0 .secondReceived :=
  ((first_reached swap).tail ⟨.output 1,.publishFirst⟩).tail ⟨.tau,.receiveSecond⟩
private theorem partials_reached (swap : Bool) : Process.Reachable ns swap left right 0 (.partialReady []) :=
  ((SourceTargetInvariantSPOT.tally_phase_is_reached swap).tail ⟨.tau,.sendTally⟩).tail ⟨.tau,.receivePartial⟩
private theorem results_reached (swap : Bool) : Process.Reachable ns swap left right 0 (.resultReady []) :=
  (partials_reached swap).tail ⟨.output 3,.publishPartial⟩

theorem first_ballot_differs_from_all_old_handles (swap : Bool) (i : Fin 1) :
    ¬ EqE ((sourceView ns swap left right .firstReceived).value i)
      (ballot ns 0 (choice swap left right 0).value) :=
  Publication.first.old_handle_distinct NumericReflectionSPOT.fixture_names_fresh (first_reached swap) i

theorem second_ballot_differs_from_all_old_handles (swap : Bool) (i : Fin 2) :
    ¬ EqE ((sourceView ns swap left right .secondReceived).value i)
      (ballot ns 1 (choice swap left right 1).value) :=
  Publication.second.old_handle_distinct NumericReflectionSPOT.fixture_names_fresh (second_reached swap) i

theorem partials_differ_from_all_old_handles (swap : Bool) (i : Fin 3) :
    ¬ EqE ((sourceView ns swap left right (.partialReady [])).value i) (sourcePartials ns swap left right []) :=
  Publication.partials.old_handle_distinct NumericReflectionSPOT.fixture_names_fresh (partials_reached swap) i

theorem results_differ_from_all_old_handles (swap : Bool) (i : Fin 4) :
    ¬ EqE ((sourceView ns swap left right (.resultReady [])).value i) (sourceResults ns swap left right []) :=
  Publication.results.old_handle_distinct NumericReflectionSPOT.fixture_names_fresh (results_reached swap) i

private theorem actual_publication {phase next : Process.Phase} {h : Nat} {m : Ground} (swap : Bool)
    (hp : Publication ns swap left right 0 phase h m next) :
    ∃ b : Named (Option (Fin phase.handles)), Named.BoundOutput (raw swap phase) (k ch.broadcast) b := by
  obtain ⟨_,hb,_⟩ := Named.restricted_output_derivable _ _ _ ((hp.scoped ch Channels.canonical_fresh).1.mapNames e k)
  exact ⟨_,hb⟩

theorem first_fresh_output_is_live (swap : Bool) :
    ∃ b : Named (Option (Fin 1)), Named.BoundOutput (raw swap .firstReceived) (k ch.broadcast) b :=
  actual_publication swap .first

theorem second_fresh_output_is_live (swap : Bool) :
    ∃ b : Named (Option (Fin 2)), Named.BoundOutput (raw swap .secondReceived) (k ch.broadcast) b :=
  actual_publication swap .second

theorem partial_fresh_output_is_live (swap : Bool) :
    ∃ b : Named (Option (Fin 3)), Named.BoundOutput (raw swap (.partialReady [])) (k ch.broadcast) b :=
  actual_publication swap .partials

theorem result_fresh_output_is_live (swap : Bool) :
    ∃ b : Named (Option (Fin 4)), Named.BoundOutput (raw swap (.resultReady [])) (k ch.broadcast) b :=
  actual_publication swap .results

/-- Old-handle exclusion is tested with nonidentity base/channel coordinates
and every possible target/label at the live result-publication phase. -/
theorem result_old_handle_output_blocked (swap : Bool) (c : Nat) (i : Fin 4) (b : Named (Fin 4)) :
    ¬ Named.FreeStep (raw swap (.resultReady [])) (.output c i) b :=
  CoordinatedPhaseOpening.canonical.no_handle_output NumericReflectionSPOT.fixture_names_fresh (results_reached swap) c i b

noncomputable abbrev padded (swap : Bool) := Named.par (raw swap (.secondReceived)) (.embed (.plain .nil))

theorem noncanonical_second_old_handle_blocked (swap : Bool) (c : Nat) (i : Fin 2) (b : Named (Fin 2)) :
    ¬ Named.FreeStep (padded swap) (.output c i) b := by
  have hj : Named.JointOpening (padded swap) (raw swap .secondReceived) :=
    (Named.restrictedState_jointOpening _).structural_left (Named.Structural.zero _).symm
  exact source_coordinated_no_handle_output ns NumericReflectionSPOT.fixture_names_fresh swap left right 0 ch
    e k .secondReceived (second_reached swap) hj c i b

abbrev collisions : Names 0 := ⟨10,11,fun _ _ => 20⟩
abbrev sameVote : CandidateSubstitution 0 Empty := left

/-- Dropping nonce freshness invalidates publication separation: the two
whole ballots are identical when both voters use the same nonce and vote. -/
theorem nonce_collision_refutes_unconditional_separation :
    EqE ((sourceView collisions false sameVote sameVote .secondReceived).value (1 : Fin 2))
      (ballot collisions 1 (choice false sameVote sameVote 1).value) := by
  exact .refl _

theorem colliding_fixture_is_not_fresh : ¬ collisions.Fresh := by
  intro hf
  have he : ((0 : Fin 2),(0 : Fin 1)) = (1,0) := hf.2.1 rfl
  have h := congrArg (fun x : Fin 2 × Fin 1 => x.1.val) he
  cases h

/-- Out-Atom remains available for the colliding value in its old frame.
The exclusion is a property of fresh election states, not a removed rule. -/
theorem colliding_old_value_can_be_emitted :
    Named.FreeStep
      (Named.restrictedState (∅ : Finset Nat)
        ⟨sourceView collisions false sameVote sameVote .secondReceived,
          .output 0 (ballot collisions 1 sameVote.value) .nil⟩)
      (.output 0 (1 : Fin 2))
      (Named.restrictedState (∅ : Finset Nat)
        ⟨sourceView collisions false sameVote sameVote .secondReceived,.nil⟩) :=
  Named.restricted_handle_output_derivable (hidden := ∅)
    (sourceView collisions false sameVote sameVote .secondReceived) 0 (1 : Fin 2) .nil (by simp)

end ExplainableCrypto.Helios.Symbolic.SourceElectionHandleSPOT
