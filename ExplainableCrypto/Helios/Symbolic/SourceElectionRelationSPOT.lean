import ExplainableCrypto.Helios.Symbolic.SourceElectionRelation
import ExplainableCrypto.Helios.Symbolic.SourceRawInternalSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceElectionRelationSPOT
open Historical General Source SourceReachableElectionSPOT

abbrev twoValues : Frame ∅ 2 := ⟨fun i => if i = 0 then .const .zero else .const .one⟩
abbrev exchange : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

theorem reindex_retains_distinct_full_values :
    (twoValues.reindex exchange).value 0 = .const .one ∧
    (twoValues.reindex exchange).value 1 = .const .zero := by decide

theorem simultaneous_reindex_retains_actual_staticEq :
    Named.StaticEq ((Named.restrictedState ∅ (⟨twoValues,.nil⟩ : ScopedState ∅ 2)).rename exchange)
      ((Named.restrictedState ∅ (⟨twoValues,.nil⟩ : ScopedState ∅ 2)).rename exchange) :=
  (Named.restrictedState_represents (hidden := ∅) (⟨twoValues,.nil⟩ : ScopedState ∅ 2)).staticEq_self.reindex exchange

theorem one_sided_reindex_is_detected : ¬ twoValues.StaticEq (twoValues.reindex exchange) := by
  intro h
  have he := (h (.var 0) (.const .zero) trivial trivial).mp (.refl _)
  exact zero_not_one he.symm

theorem actual_initial_pair_is_related (swap swap' : Bool) :
    SourceElectionRelation initial ns left right 1 ch (initial swap) (initial swap') :=
  SourceElectionRelation.initial ns NumericReflectionSPOT.fixture_names_fresh swap swap'
    left right (by unfold NoncesFreshFor; decide) (by unfold NoncesFreshFor; decide) 1 ch

private theorem waiting_related (swap swap' : Bool) :
    SourceElectionRelation initial ns left right 1 ch (raw swap (.input [])) (raw swap' (.input [])) := by
  have hj (s : Bool) : Named.JointOpening ((raw s (.input [])).rename (Equiv.refl (Fin 3)))
      (Named.mappedState ch.privateChannels (sourceState ns s left right 1 ch (.input []))
        (Equiv.refl Nat) (Equiv.refl Nat)) := by
    change Named.JointOpening ((raw s (.input [])).rename id) _
    rw [Named.rename_id]
    have hid := Named.mappedState_identity ch.privateChannels
      (sourceState ns s left right 1 ch (.input []))
    exact (congrArg (Named.JointOpening (raw s (.input []))) hid).mpr
      (Named.restrictedState_jointOpening _)
  have hp (s : Bool) : ((raw s (.input [])).rename (Equiv.refl (Fin 3))).RepresentsFrame
      (ch.privateChannels.image (Equiv.refl Nat)) ((sourceView ns s left right (.input [])).mapNames (Equiv.refl Nat)) := by
    have ht : Named.Structural (raw s (.input []))
        (Named.mappedState ch.privateChannels (sourceState ns s left right 1 ch (.input []))
          (Equiv.refl Nat) (Equiv.refl Nat)) := by
      have hid := Named.mappedState_identity ch.privateChannels
        (sourceState ns s left right 1 ch (.input []))
      exact (congrArg (Named.Structural (raw s (.input []))) hid).mpr (.refl _)
    have hp := (Named.restrictedState_represents (hidden := ch.privateChannels)
      (sourceState ns s left right 1 ch (.input []))).transport_state_structure ht
    change ((raw s (.input [])).rename id).RepresentsFrame _ _
    rw [Named.rename_id]; exact hp
  exact ⟨swap,swap',.input [],Equiv.refl _,Equiv.refl _,Equiv.refl _,
    SourceCoordinatedSPOT.waiting_phase_is_reached swap,SourceCoordinatedSPOT.waiting_phase_is_reached swap',
    actual_two_publications swap,actual_two_publications swap',hj swap,hj swap',hp swap,hp swap'⟩

/-- The same relation survives an actual replay input and its rejection, with
both full successor frames. Expected rejection comes from the retained replay
fixture, not from the matching implementation. -/
theorem replay_input_then_rejection_preserves_one_relation (swap swap' : Bool) :
    ∃ b d, Named.FreeStep (raw swap' (.input [])) (.input 4 (.var (1 : Fin 3))) b ∧
      Named.Reduction b d ∧ SourceElectionRelation initial ns left right 1 ch (raw swap (.rejected [])) d ∧
      Named.StaticEq (raw swap (.rejected [])) d := by
  obtain ⟨b,hb,hr⟩ := (waiting_related swap swap').input NumericReflectionSPOT.fixture_names_fresh
    Channels.canonical_fresh (actual_replay_input swap)
  obtain ⟨d,hd,ht⟩ := hr.internal NumericReflectionSPOT.fixture_names_fresh Channels.canonical_fresh
    (actual_replay_rejection swap)
  exact ⟨b,d,hb,hd,ht,ht.staticEq NumericReflectionSPOT.fixture_names_fresh⟩

theorem reached_handle_permutation_preserves_one_relation (swap swap' : Bool) :
    SourceElectionRelation initial ns left right 1 ch
      ((raw swap (.input [])).rename (Equiv.swap (0 : Fin 3) (2 : Fin 3)))
      ((raw swap' (.input [])).rename (Equiv.swap (0 : Fin 3) (2 : Fin 3))) :=
  (waiting_related swap swap').reindex (Equiv.swap (0 : Fin 3) (2 : Fin 3))

theorem missing_export_cannot_enter_relation (a : Named (Fin 1)) :
    ¬ SourceElectionRelation initial ns left right 1 ch (.embed (.plain .nil)) a := by
  intro h
  exact (h.staticEq NumericReflectionSPOT.fixture_names_fresh).complete_domains.1 0

end ExplainableCrypto.Helios.Symbolic.SourceElectionRelationSPOT
