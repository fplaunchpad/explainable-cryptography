import ExplainableCrypto.Helios.Symbolic.SourceRawOutputMatching
import ExplainableCrypto.Helios.Symbolic.SourceCoordinatedSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceRawVisibleSPOT
open Historical General Source

abbrev zeroFrame : Frame ∅ 1 := ⟨fun _ => .const .zero⟩
abbrev receiving : ScopedState ∅ 1 := ⟨zeroFrame,.input 7 (.output 8 (.var none) .nil)⟩
abbrev sending : ScopedState ∅ 1 := ⟨zeroFrame,.output 8 (.spk (.name 40) (.name 41) (.const .one) (.name 42)) .nil⟩
abbrev fullRecipe : Recipe 1 := .spk (.name 40) (.name 41) (.var 0) (.binary .pair (.var 0) (.name 42))
noncomputable abbrev padded {h : Nat} (a : Named (Fin h)) := Named.par a (.embed (.plain .nil))

private theorem padded_joint {policy channels : Finset Nat} {h : Nat} (p : ScopedState policy h) :
    Named.JointOpening (padded (Named.restrictedState channels p)) (Named.restrictedState channels p) :=
  (Named.restrictedState_jointOpening p).structural_left (Named.Structural.zero _).symm

theorem ready_raw_input_keeps_the_full_recipe :
    ∃ b, Named.FreeStep (padded (Named.restrictedState ∅ receiving)) (.input 7 fullRecipe) b :=
  (padded_joint receiving).input_available (by simp) rfl fullRecipe

theorem ready_raw_output_exports_a_fresh_domain :
    ∃ b : Named (Option (Fin 1)), Named.BoundOutput (padded (Named.restrictedState ∅ sending)) 8 b :=
  (padded_joint sending).bound_available (by simp) rfl

theorem prefix_blocks_nested_actions :
    ¬ (Agent.input 7 (.output 8 (.var none) .nil) : Agent (Fin 1)).HasOutput 8 ∧
    ¬ (Agent.output 8 (.var (0 : Fin 1)) (.input 7 .nil)).HasInput 7 := by
  exact ⟨not_false,not_false⟩

theorem wrong_ready_channel_is_excluded :
    ¬ receiving.body.HasInput 8 ∧ ¬ sending.body.HasOutput 7 := by
  change (¬ (8 : Nat) = 7) ∧ ¬ (7 : Nat) = 8
  decide

theorem private_ready_input_cannot_escape (b : Named (Fin 1)) :
    receiving.body.HasInput 7 ∧
      ¬ Named.FreeStep (padded (Named.restrictedState {7} receiving)) (.input 7 fullRecipe) b :=
  ⟨rfl,(padded_joint receiving).private_free_blocked receiving (.input 7 fullRecipe) (by simp [Extended.FreeLabel.channel])⟩

theorem private_ready_output_cannot_escape (b : Named (Option (Fin 1))) :
    sending.body.HasOutput 8 ∧
      ¬ Named.BoundOutput (padded (Named.restrictedState {8} sending)) 8 b :=
  ⟨rfl,(padded_joint sending).private_bound_blocked sending 8 (by simp)⟩

open SourceCoordinatedSPOT

/-- Nonidentity private coordinates and a formerly private literal are retained
while the matching action starts in the padded raw partner itself. -/
theorem actual_old_literal_input_matches_raw_partner (swap swap' : Bool) :
    ∃ t, Named.FreeStep (padded (raw swap' (.input []))) (.input (ch.voter 2) oldLiteral) t ∧
      Named.StaticEq (raw swap (.check [] originalRecipe)) t := by
  obtain ⟨f,l,next,hh,t,ht,_,_,_,_,_,_,hs⟩ := source_reachable_input_match ns
    NumericReflectionSPOT.fixture_names_fresh swap swap' left right 1 ch Channels.canonical_fresh
    e k (.input []) (waiting_phase_is_reached swap) (Named.restrictedState_jointOpening _)
    (padded_joint _) (Named.restrictedState_represents _)
    ((Named.restrictedState_represents _).structural (Named.Structural.zero _).symm)
    (actual_old_literal_input swap)
  exact ⟨t,ht,hs⟩

/-- Real ballot publication obtains an actual raw-partner fresh output and
statically equivalent complete successor frames in either voting direction. -/
theorem actual_ballot_output_matches_raw_partner (swap swap' : Bool) :
    ∃ (b t : Named (Option (Fin 1))) (next : Process.Phase) (hh : 2 = next.handles),
      Named.BoundOutput (raw swap .firstReceived) (k ch.broadcast) b ∧
      Named.BoundOutput (padded (raw swap' .firstReceived)) (k ch.broadcast) t ∧
      Named.StaticEq ((b.rename Extended.outputHandle).rename (Fin.cast hh))
        ((t.rename Extended.outputHandle).rename (Fin.cast hh)) := by
  obtain ⟨b,hb,_⟩ := actual_output_uses_current_coordinates swap
  have hr : Process.Reachable ns swap left right 1 .firstReceived :=
    Relation.ReflTransGen.refl.tail ⟨.tau,.receiveFirst⟩
  obtain ⟨next,hh,t,ht,_,_,_,_,_,_,hs⟩ := source_reachable_bound_match ns
    NumericReflectionSPOT.fixture_names_fresh swap swap' left right 1 ch Channels.canonical_fresh
    e k .firstReceived hr (Named.restrictedState_jointOpening _) (padded_joint _)
    (Named.restrictedState_represents _)
    ((Named.restrictedState_represents _).structural (Named.Structural.zero _).symm) hb
  exact ⟨b,t,next,hh,hb,ht,hs⟩

end ExplainableCrypto.Helios.Symbolic.SourceRawVisibleSPOT
