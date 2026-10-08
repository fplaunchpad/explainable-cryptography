import ExplainableCrypto.Helios.Symbolic.SourceCoordinatedFreshInput
import ExplainableCrypto.Helios.Symbolic.SourceCoordinatedOutput
import ExplainableCrypto.Helios.Symbolic.SourceJointVisibleSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceCoordinatedSPOT
open Historical General Source
abbrev ns := SharedTallySPOT.names
abbrev left := SharedTallySPOT.left
abbrev right := SharedTallySPOT.right
abbrev ch := Channels.canonical
abbrev e : Nat ≃ Nat := Equiv.swap ns.secretKey 100
abbrev k : Nat ≃ Nat := Equiv.swap ch.trustee 200
abbrev f : Nat ≃ Nat := Equiv.swap 100 101
abbrev l : Nat ≃ Nat := Equiv.swap 200 201
abbrev es (swap : Bool) (phase : Process.Phase) := sourceState ns swap left right 1 ch phase
noncomputable abbrev raw (swap : Bool) (phase : Process.Phase) := Named.mappedState ch.privateChannels (es swap phase) e k
abbrev oldLiteral : Recipe 3 := .name ns.secretKey
abbrev originalRecipe : Recipe 3 := .name 100

theorem composition_moves_secret_in_forward_order : (e.trans f) ns.secretKey = 101 := by decide

theorem reversed_composition_is_different : (e.trans f) ns.secretKey ≠ (f.trans e) ns.secretKey := by decide

theorem complete_mapped_state_composes (swap : Bool) (phase : Process.Phase) :
    Named.mappedState (ch.privateChannels.image k) ((es swap phase).mapNames e k) f l =
      Named.mappedState ch.privateChannels (es swap phase) (e.trans f) (k.trans l) :=
  Named.mappedState_comp _ _ _ _ _ _

theorem original_literal_is_private : ¬ oldLiteral.Public ns.restricted := by
  change ¬ ns.secretKey ∉ ns.restricted
  decide

theorem old_literal_is_public_in_current_coordinates : oldLiteral.Public (ns.restricted.image e) := by
  change ns.secretKey ∉ ns.restricted.image e
  decide

theorem inverse_recipe_is_fresh_public_name : oldLiteral.mapNames e.symm = originalRecipe := by decide

theorem inverse_recipe_is_public : originalRecipe.Public ns.restricted := by
  change 100 ∉ ns.restricted
  decide

theorem literal_recipe_round_trip : originalRecipe.mapNames e = oldLiteral := by decide

theorem public_voter_channel_stays_literal : k (ch.voter 2) = ch.voter 2 := by decide

theorem waiting_phase_is_reached (swap : Bool) : Process.Reachable ns swap left right 1 (.input []) := by
  have h : Process.Reachable ns swap left right 1 (Process.afterAccepted 1 []) :=
    (((Relation.ReflTransGen.refl.tail ⟨.tau,Process.Step.receiveFirst⟩).tail
      ⟨.output 1,Process.Step.publishFirst⟩).tail ⟨.tau,Process.Step.receiveSecond⟩).tail
      ⟨.output 2,Process.Step.publishSecond⟩
  exact h

theorem actual_old_literal_input (swap : Bool) :
    Named.FreeStep (raw swap (.input [])) (.input (ch.voter 2) oldLiteral) (raw swap (.check [] originalRecipe)) := by
  have hs : ScopedStep ch.privateChannels ns.restricted (es swap (.input []))
      (.input (ch.voter 2) originalRecipe) (es swap (.check [] originalRecipe)) :=
    .input _ _ _ ((Channels.voter_public_iff Channels.canonical_fresh _).mpr (by decide)) inverse_recipe_is_public
      (residual_visible_input ns swap left right 1 ch [] originalRecipe (by decide))
  have hm := hs.mapNames e k
  change ScopedStep _ _ _ (.input (k (ch.voter 2)) (originalRecipe.mapNames e)) _ at hm
  rw [public_voter_channel_stays_literal,literal_recipe_round_trip] at hm
  exact Named.restricted_input_derivable _ _ _ _ hm

theorem actual_input_reaches_coordinated_check (swap : Bool) :
    CoordinatedPhaseOpening ns swap left right 1 ch e k (.check [] originalRecipe) (raw swap (.check [] originalRecipe)) := by
  obtain ⟨rs,s,hphase,he,_,_,_,ht⟩ := source_coordinated_public_input_next ns swap left right 1 ch Channels.canonical_fresh
    e k (.input []) (by change (0 : Nat) < 1; decide) (Named.restrictedState_jointOpening _) (actual_old_literal_input swap)
    old_literal_is_public_in_current_coordinates
  cases hphase
  have hs : s = originalRecipe := (eq_of_heq he).symm.trans inverse_recipe_is_fresh_public_name
  subst s
  exact ht

/-- The common-refresh result is exercised from nonidentity current coordinates,
including a matching actual input from the other fresh canonical vote world. -/
theorem both_worlds_refresh_and_match_check (swap swap' : Bool) :
    ∃ (f' l' : Nat ≃ Nat) (s : Recipe 3), s.Public ns.restricted ∧
      Process.Step ns swap left right 1 (.input []) (.input 2 s) (.check [] s) ∧
      Process.Reachable ns swap left right 1 (.check [] s) ∧
      CoordinatedPhaseOpening ns swap left right 1 ch (e.trans f') (k.trans l') (.check [] s) (raw swap (.check [] originalRecipe)) ∧
      ∃ t : Named (Fin 3),
        Named.FreeStep (Named.mappedState ch.privateChannels (es swap' (.input [])) (e.trans f') (k.trans l'))
          (.input (ch.voter 2) oldLiteral) t ∧
        CoordinatedPhaseOpening ns swap' left right 1 ch (e.trans f') (k.trans l') (.check [] s) t := by
  obtain ⟨f',l',rs,s,hphase,_,hp,_,hs,hr,ht,_,_,_,hm⟩ := source_coordinated_common_input_next ns
    NumericReflectionSPOT.fixture_names_fresh swap swap' left right 1 ch Channels.canonical_fresh e k
    (.input []) (waiting_phase_is_reached swap) (Named.restrictedState_jointOpening _)
    (Named.restrictedState_jointOpening _) (actual_old_literal_input swap)
  cases hphase
  exact ⟨f',l',s,hp,hs,hr,ht,hm⟩

theorem input_does_not_decide_acceptance (swap : Bool) :
    Process.Step ns swap left right 1 (.input []) (.input 2 originalRecipe) (.check [] originalRecipe) :=
  .input (by decide) inverse_recipe_is_public

/-- A real internal transition follows the input; either guard outcome retains
current coordinates on the whole raw target. -/
theorem actual_internal_after_input_retains_coordinates (swap : Bool) :
    ∃ (b : Named (Fin 3)) (next : Process.Phase),
      Named.Reduction (raw swap (.check [] originalRecipe)) b ∧
      Process.Step ns swap left right 1 (.check [] originalRecipe) .tau next ∧
      CoordinatedPhaseOpening ns swap left right 1 ch e k next b := by
  classical
  have hs : ∃ next, Process.Step ns swap left right 1 (.check [] originalRecipe) .tau next := by
    by_cases h : Process.accepts ns swap left right [] originalRecipe
    · exact ⟨_,.accept h⟩
    · exact ⟨_,.reject h⟩
  obtain ⟨next,hs⟩ := hs
  have ht : ScopedStep ch.privateChannels ns.restricted (es swap (.check [] originalRecipe)) .tau
      ⟨sourceView ns swap left right (.check [] originalRecipe),residual ns swap left right 1 ch next⟩ :=
    .tau _ (residual_tau_step ns swap left right 1 ch hs)
  have hraw := Named.restricted_tau_derivable _ _ (ht.mapNames e k)
  obtain ⟨next',hs',hb⟩ := (actual_input_reaches_coordinated_check swap).internal Channels.canonical_fresh (by change (0 : Nat) < 1; decide) hraw
  exact ⟨_,next',hraw,hs',hb⟩

theorem private_trustee_stays_blocked_after_input (swap : Bool) (b : Named (Option (Fin 3))) :
    ¬ Named.BoundOutput (raw swap (.check [] originalRecipe)) 200 b := by
  intro h
  exact (actual_input_reaches_coordinated_check swap).bound_channel_public h (by decide)

theorem actual_output_uses_current_coordinates (swap : Bool) :
    ∃ b : Named (Option (Fin 1)), Named.BoundOutput (raw swap .firstReceived) (k ch.broadcast) b ∧
      CoordinatedPhaseOpening ns swap left right 1 ch e k .firstPublished (b.rename Extended.outputHandle) := by
  have hp := (Publication.first (ns := ns) (swap := swap) (left := left) (right := right) (extra := 1)).scoped
    ch Channels.canonical_fresh
  obtain ⟨m,hm,_⟩ := Named.restricted_output_derivable _ _ _ (hp.1.mapNames e k)
  obtain ⟨handle,value,next,hpub,_,_,ht⟩ := source_coordinated_output_next ns swap left right 1 ch Channels.canonical_fresh
    e k .firstReceived (by trivial) (Named.restrictedState_jointOpening _) hm
  cases hpub
  exact ⟨_,hm,ht⟩

theorem full_fourth_input_field_is_not_discarded :
    SourceName.base 48 ∈ (Extended.FreeLabel.input 0 SourceOperationalPrenexSPOT.proofRecipe).nameSupport :=
  SourceOperationalPrenexSPOT.fourth_field_in_label_support

theorem stale_policy_cannot_justify_original_input (swap : Bool) :
    ¬ Process.Step ns swap left right 1 (.input []) (.input 2 oldLiteral) (.check [] oldLiteral) := by
  intro h
  exact original_literal_is_private h.input_scope.2.1

theorem every_internal_trace_after_input_retains_coordinates (swap : Bool) {b : Named (Fin 3)}
    (h : Relation.ReflTransGen (@Named.Reduction (Fin 3)) (raw swap (.check [] originalRecipe)) b) :
    ∃ next, Process.Reachable ns swap left right 1 next ∧
      Relation.ReflTransGen (fun p q => Process.Step ns swap left right 1 p .tau q) (.check [] originalRecipe) next ∧
      CoordinatedPhaseOpening ns swap left right 1 ch e k next b :=
  (actual_input_reaches_coordinated_check swap).internal_trace Channels.canonical_fresh
    ((waiting_phase_is_reached swap).tail ⟨.input 2 originalRecipe,input_does_not_decide_acceptance swap⟩) h

end ExplainableCrypto.Helios.Symbolic.SourceCoordinatedSPOT
