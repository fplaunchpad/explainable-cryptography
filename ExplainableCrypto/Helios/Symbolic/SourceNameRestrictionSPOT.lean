import ExplainableCrypto.Helios.Symbolic.SourceNameRestrictionBridge
import ExplainableCrypto.Helios.Symbolic.SourceScopedSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceNameRestrictionSPOT
open Historical General Source

abbrev outputPair : Named Empty := .embed (.plain (.output 0 (.binary .pair (.name 40) (.name 41)) .nil))

theorem binder_removes_only_own_sort :
    (Named.newName (.base 40) (.embed (.plain (.output 40 (.name 40) .nil))) : Named Empty).freeNames =
      {SourceName.channel 40} := by
  decide

theorem fresh_name_extrusion :
    Named.Structural (.par outputPair (.newName (.base 42) outputPair))
      (.newName (.base 42) (.par outputPair outputPair)) :=
  .namePar _ _ _ (by decide)

/-- This checks the rule's actual side condition, not nonexistence of every
possible structural derivation in the full equivalence closure. -/
theorem capturing_extrusion_side_condition_fails :
    ¬ (SourceName.base 40 ∉ outputPair.freeNames) := by decide

theorem fresh_base_alpha_changes_payload :
    Named.Structural (.newName (.base 40) outputPair)
      (.newName (.base 42) (.embed (.plain (.output 0 (.binary .pair (.name 42) (.name 41)) .nil)))) := by
  simpa [outputPair,Named.mapNames,SourceName.map,Extended.mapNames,Agent.mapNames,Term.mapNames,Equiv.swap_apply_def] using
    Named.Structural.alphaBase outputPair 40 42 (by decide)

theorem fresh_channel_alpha_keeps_base_literal :
    Named.Structural
      (.newName (.channel 0) (.embed (.plain (.output 0 (.name 0) .nil))) : Named Empty)
      (.newName (.channel 7) (.embed (.plain (.output 7 (.name 0) .nil)))) := by
  simpa [Named.mapNames,SourceName.map,Extended.mapNames,Agent.mapNames,Term.mapNames] using
    Named.Structural.alphaChannel (.embed (.plain (.output 0 (.name 0) .nil)) : Named Empty) 0 7 (by decide)

theorem nested_binder_alpha_freshness_fails :
    ¬ (SourceName.base 42 ∉ (Named.newName (.base 42) outputPair).allNames) := by decide

theorem fourth_proof_field_blocks_input_scope :
    SourceName.base 40 ∈ (Extended.FreeLabel.input 0
      (.spk (.name 41) (.name 42) (.const .one) (.binary .pair (.name 43) (.name 40))) : Extended.FreeLabel (Fin 1)).nameSupport := by
  decide

theorem private_channel_blocks_label_scope :
    SourceName.channel 7 ∈ (Extended.FreeLabel.output 7 (0 : Fin 1)).nameSupport ∧
    SourceName.channel 7 ∈ (Extended.FreeLabel.input 7 (.var (0 : Fin 1))).nameSupport := by decide

theorem public_handle_crosses_base_scope :
    SourceName.base 40 ∉ (Extended.FreeLabel.input 0 (.var (0 : Fin 1))).nameSupport := by decide

/-- Secret-bearing data crosses name Scope through a bound base variable;
the secret name remains restricted around the full active output binding. -/
theorem full_secret_output_retains_restriction :
    Named.BoundOutput (.newName (.base 40) outputPair) 0
      (.newName (.base 40) (.embed (.par (.active none (.binary .pair (.name 40) (.name 41))) (.plain .nil)))) :=
  .scopeName _ (by decide) (.embed (Extended.message_output _ _ _))

theorem private_communication_inside_binder :
    Named.Reduction
      (.newName (.channel 7) (.embed (.plain (.par (.output 7 (.name 40) .nil) (.input 7 (.output 0 (.var none) .nil))))) : Named Empty)
      (.newName (.channel 7) (.embed (.plain (.par .nil (.output 0 (.name 40) .nil))))) :=
  .newName _ (.embed (Extended.message_communication _ _ _ _))

theorem unused_name_binder_eliminates :
    Named.Structural (.newName (.base 40) (.embed (.plain .nil)) : Named Empty) (.embed (.plain .nil)) :=
  .nameZero _

theorem actual_voter_input_has_name_scope (swap : Bool) :
    Named.FreeStep
      (Named.restrictedState Channels.canonical.privateChannels
        ⟨SharedTallySPOT.world swap,residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right
          1 Channels.canonical (.input [])⟩)
      (.input 4 (.var 1))
      (Named.restrictedState Channels.canonical.privateChannels
        ⟨SharedTallySPOT.world swap,residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right
          1 Channels.canonical (.check [] (.var 1))⟩) :=
  Named.restricted_input_derivable _ _ _ _ (SourceScopedSPOT.actual_voter_input swap)

theorem raw_output_and_capture_have_name_scope :
    ∃ m : Ground,
      Named.BoundOutput (Named.restrictedState Channels.canonical.privateChannels SourceScopedSPOT.emitting) 0
        (Named.restrictedCapture Channels.canonical.privateChannels SourceScopedSPOT.publicFrame m .nil) ∧
      Named.Structural
        ((Named.restrictedCapture Channels.canonical.privateChannels SourceScopedSPOT.publicFrame m .nil).rename Extended.outputHandle)
        (Named.restrictedState Channels.canonical.privateChannels SourceScopedSPOT.emitted) :=
  Named.restricted_output_derivable _ _ _ SourceScopedSPOT.output_exposes_full_value.1
end ExplainableCrypto.Helios.Symbolic.SourceNameRestrictionSPOT
