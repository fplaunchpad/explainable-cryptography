import ExplainableCrypto.Helios.Symbolic.SourceInputPresentationClosure
import ExplainableCrypto.Helios.Symbolic.SourceReachableElectionSPOT
import ExplainableCrypto.Helios.Symbolic.SourceFrameCompatibilitySPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceInputPresentationSPOT
open Historical General Source

/-- A currently private literal forces actual key freshening. The original raw
state still has a full presentation at the new policy and the full pk value. -/
theorem formerly_private_literal_gets_actual_new_presentation :
    ∃ e k : Nat ≃ Nat,
      e 40 ≠ 40 ∧ (Term.name 40 : Recipe 1).Public (({40} : Finset Nat).image e) ∧
      (Named.restrictedState {7} SourceFreshNamesSPOT.receiving).RepresentsFrame
        (({7} : Finset Nat).image k) (SourceFreshNamesSPOT.receiving.frame.mapNames e) ∧
      (SourceFreshNamesSPOT.receiving.frame.mapNames e).value 0 = .unary .pk (.name (e 40)) := by
  obtain ⟨e,k,hp,hr,_,he,hv⟩ := SourceFreshNamesSPOT.old_literal_gets_fresh_policy_and_retained_key
  exact ⟨e,k,he,hr,(Named.restrictedState_represents SourceFreshNamesSPOT.receiving).transport_state_structure hp,hv⟩

theorem formerly_private_literal_rejects_stale_policy : ¬ (Term.name 40 : Recipe 1).Public {40} := by
  simp [Term.Public]

open SourceCoordinatedSPOT

theorem actual_election_input_retains_both_presentations (swap swap' : Bool) :
    ∃ (f' l' : Nat ≃ Nat) (s : Recipe 3),
      Process.Reachable ns swap left right 1 (.check [] s) ∧
      CoordinatedPhaseOpening ns swap left right 1 ch (e.trans f') (k.trans l') (.check [] s)
        (raw swap (.check [] originalRecipe)) ∧
      (raw swap (.check [] originalRecipe)).RepresentsFrame (ch.privateChannels.image (k.trans l'))
        ((sourceView ns swap left right (.input [])).mapNames (e.trans f')) ∧
      (raw swap' (.input [])).RepresentsFrame (ch.privateChannels.image (k.trans l'))
        ((sourceView ns swap' left right (.input [])).mapNames (e.trans f')) ∧
      Named.StaticEq (raw swap (.check [] originalRecipe)) (raw swap' (.input [])) := by
  obtain ⟨f',l',rs,s,hphase,_,_,_,_,hr,ht,hb,hd,_,hs⟩ := source_coordinated_input_presented_next
    ns NumericReflectionSPOT.fixture_names_fresh swap swap' left right 1 ch Channels.canonical_fresh
    e k (.input []) (waiting_phase_is_reached swap) (Named.restrictedState_jointOpening _)
    (Named.restrictedState_jointOpening _) (Named.restrictedState_represents _)
    (Named.restrictedState_represents _) (actual_old_literal_input swap)
  cases hphase
  exact ⟨f',l',s,hr,ht,hb,hd,hs⟩

/-- The already constructed actual rejection is the internal induction case;
its entire three-handle frame survives at the actual reached successor. -/
theorem actual_rejection_retains_presented_successor (swap : Bool) :
    ∃ (next : Process.Phase) (hh : 3 = next.handles),
      Process.Step ns swap left right 1 (.check [] (.var 1)) .tau next ∧
      Process.Reachable ns swap left right 1 next ∧
      Named.JointOpening ((SourceReachableElectionSPOT.raw swap (.rejected [])).rename (Fin.cast hh))
        (Named.mappedState ch.privateChannels (sourceState ns swap left right 1 ch next)
          (Equiv.refl Nat) (Equiv.refl Nat)) ∧
      ((SourceReachableElectionSPOT.raw swap (.rejected [])).rename (Fin.cast hh)).RepresentsFrame
        (ch.privateChannels.image (Equiv.refl Nat))
        ((sourceView ns swap left right next).mapNames (Equiv.refl Nat)) := by
  apply source_coordinated_internal_presented_next ns swap left right 1 ch Channels.canonical_fresh
    (Equiv.refl Nat) (Equiv.refl Nat) (.check [] (.var 1))
    ((waiting_phase_is_reached swap).tail ⟨.input 2 (.var 1),.input (by decide) trivial⟩)
    (a := SourceReachableElectionSPOT.raw swap (.check [] (.var 1)))
  · simpa only [Named.mappedState_identity] using Named.restrictedState_jointOpening
      (hidden := ch.privateChannels) (sourceState ns swap left right 1 ch (.check [] (.var 1)))
  · have hs : Named.Structural (SourceReachableElectionSPOT.raw swap (.check [] (.var 1)))
        (Named.mappedState ch.privateChannels (sourceState ns swap left right 1 ch (.check [] (.var 1)))
          (Equiv.refl Nat) (Equiv.refl Nat)) := by
      rw [Named.mappedState_identity]
      exact .refl _
    exact (Named.restrictedState_represents (hidden := ch.privateChannels)
      (sourceState ns swap left right 1 ch (.check [] (.var 1)))).transport_state_structure hs
  · exact SourceReachableElectionSPOT.actual_replay_rejection swap

theorem frame_only_output_route_is_not_available :
    SourceFrameCompatibilitySPOT.latentPrivateOutput.RepresentsFrame ∅ SourceFrameCompatibilitySPOT.emptyPublicFrame ∧
    Named.BoundOutput SourceFrameCompatibilitySPOT.latentPrivateOutput 0 SourceFrameCompatibilitySPOT.latentPrivateCapture ∧
    ¬ ∃ (hidden : Finset Nat) (φ : Frame ∅ 1),
      SourceFrameCompatibilitySPOT.latentPrivateTarget.RepresentsFrame hidden φ :=
  ⟨SourceFrameCompatibilitySPOT.latent_private_name_is_absent_from_old_frame_policy,
    SourceFrameCompatibilitySPOT.latent_private_name_has_actual_output,
    fun ⟨hidden,φ,h⟩ => SourceFrameCompatibilitySPOT.latent_private_capture_has_no_empty_policy hidden φ h⟩

end ExplainableCrypto.Helios.Symbolic.SourceInputPresentationSPOT
