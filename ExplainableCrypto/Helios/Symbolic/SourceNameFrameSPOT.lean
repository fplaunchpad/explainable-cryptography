import ExplainableCrypto.Helios.Symbolic.SourceNameFrameEmbedding
import ExplainableCrypto.Helios.Symbolic.SourceNameSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceNameFrameSPOT
open Historical General Source Extended SourceNameSPOT

def original : Frame ({0} : Finset Nat) 1 := ⟨fun _ => .unary .pk (.name 0)⟩
abbrev moved := original.mapNames baseSwap

theorem complete_frame_values :
    (moved.extend (.name 40)).value 0 = .unary .pk (.name 40) ∧
    (moved.extend (.name 40)).value 1 = .name 40 := by
  refine ⟨?_,rfl⟩
  change (Term.unary .pk (.name (baseSwap 0)) : Ground) = .unary .pk (.name 40)
  simp [baseSwap]

theorem compound_recipe_keeps_old_handle :
    moved.eval (.binary .pair (.var 0) (.name 41)) =
      .binary .pair (.unary .pk (.name 40)) (.name 41) := by
  simp [Frame.eval,Frame.mapNames,original,Term.subst,Term.mapNames,baseSwap]

/-- A deliberately leaking process exports the full renamed secret, even
though the literal is not a public input recipe. -/
theorem secret_output_moves :
    ScopedStep (({0} : Finset Nat).image channelSwap) (({0} : Finset Nat).image baseSwap)
      ⟨moved,.output 1 (.name 40) .nil⟩ (.output 1) ⟨moved.extend (.name 40),.nil⟩ := by
  have h : ScopedStep ({0} : Finset Nat) ({0} : Finset Nat)
      ⟨original,.output 1 (.name 0) .nil⟩ (.output 1) ⟨original.extend (.name 0),.nil⟩ :=
    .output _ _ _ (by decide) (Agent.Visible.of_core (.output _ _ _))
  simpa [ScopedState.mapNames,PublicEvent.mapNames,Frame.mapNames_extend,Agent.mapNames,Term.mapNames,
    baseSwap,channelSwap,Equiv.swap_apply_def] using h.mapNames baseSwap channelSwap

theorem renamed_private_output_blocked (q : ScopedState (({0} : Finset Nat).image baseSwap) 2) :
    ¬ ScopedStep (({0} : Finset Nat).image channelSwap) (({0} : Finset Nat).image baseSwap)
      ⟨moved,.output 7 (.name 40) .nil⟩ (.output 7) q := by
  apply scoped_private_output_blocked
  simp [channelSwap]

/-- Keeping the old channel policy really admits the forbidden output. -/
theorem stale_private_policy_allows_output :
    ScopedStep ({0} : Finset Nat) (({0} : Finset Nat).image baseSwap)
      ⟨moved,.output 7 (.name 40) .nil⟩ (.output 7) ⟨moved.extend (.name 40),.nil⟩ :=
  .output _ _ _ (by decide) (Agent.Visible.of_core (.output _ _ _))

theorem full_active_frame_moves :
    (activeFrame (original.extend (.name 0))).mapNames baseSwap channelSwap =
      .par (.active (1 : Fin 2) (.name 40))
        (.par (.active 0 (.unary .pk (.name 40))) (.plain .nil)) := by
  change Extended.par (.active (1 : Fin 2) (.name (baseSwap 0)))
    (.par (.active 0 (.unary .pk (.name (baseSwap 0)))) (.plain .nil)) = _
  simp [baseSwap]

/-- Public observations can distinguish changing an output to a public
literal. This uses the new handle and a public recipe, not tally equality. -/
theorem replaced_output_is_observable :
    ¬ (moved.extend (.name 40)).StaticEq (moved.extend (.name 41)) := by
  intro h
  have hr : (Term.name 41 : Recipe 2).Public (({0} : Finset Nat).image baseSwap) := by
    simp [Term.Public,baseSwap]
  have he := (h (.var 1) (.name 41) trivial hr).mpr (EqE.refl (.name 41))
  have hn := (EqE.name_iff 40 41).mp he
  omega

theorem private_handshake_still_internal :
    ScopedStep (({0} : Finset Nat).image channelSwap) (({0} : Finset Nat).image baseSwap)
      ⟨moved,.par (.output 7 (.name 40) .nil) (.input 7 (.output 1 (.var none) .nil))⟩ .tau
      ⟨moved,.par .nil (.output 1 (.name 40) .nil)⟩ :=
  .tau _ (Agent.Tau.of_core (.comm _ _ _ _))

theorem compound_public_input_evaluates :
    ScopedStep (({0} : Finset Nat).image channelSwap) (({0} : Finset Nat).image baseSwap)
      ⟨moved,.input 1 (.output 1 (.var none) .nil)⟩ (.input 1 (.binary .pair (.var 0) (.name 41)))
      ⟨moved,.output 1 (.binary .pair (.unary .pk (.name 40)) (.name 41)) .nil⟩ := by
  apply ScopedStep.input _ _ _ (by simp [channelSwap]) (by simp [Term.Public,baseSwap])
  rw [compound_recipe_keeps_old_handle]
  exact Agent.Visible.of_core (.input _ _ _)

theorem actual_reached_observations_move {p : Process.Phase}
    (h : Process.Reachable SharedTallySPOT.names false SharedTallySPOT.left SharedTallySPOT.right 1 p) :
    ((sourceView SharedTallySPOT.names false SharedTallySPOT.left SharedTallySPOT.right p).mapNames baseSwap).StaticEq
      ((sourceView SharedTallySPOT.names true SharedTallySPOT.left SharedTallySPOT.right p).mapNames baseSwap) :=
  (reachable_source_view_staticEq NumericReflectionSPOT.fixture_names_fresh h).mapNames baseSwap
end ExplainableCrypto.Helios.Symbolic.SourceNameFrameSPOT
