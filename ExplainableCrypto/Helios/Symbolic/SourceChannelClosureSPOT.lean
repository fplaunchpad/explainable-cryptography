import ExplainableCrypto.Helios.Symbolic.SourceChannelPreservation
import ExplainableCrypto.Helios.Symbolic.SourceNameRestrictionSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceChannelClosureSPOT
open Historical General Source

abbrev hiddenSender : Named Empty := .newName (.channel 7) (.embed (.plain (.output 7 (.name 40) .nil)))
abbrev privateExchange : Named Empty := .newName (.channel 7)
  (.embed (.plain (.par (.output 7 (.name 40) .nil) (.input 7 (.output 0 (.var none) .nil)))))

theorem hidden_sender_has_no_free_channels : hiddenSender.channels = ∅ := by decide

theorem arbitrary_rearrangement_cannot_expose_private_output (a : Named Empty)
    (hs : Named.Structural hiddenSender a) (q : Named (Option Empty)) :
    ¬ Named.BoundOutput a 7 q := by
  intro h
  have hc := h.channel_mem
  rw [← hs.channels,hidden_sender_has_no_free_channels] at hc
  exact Finset.notMem_empty _ hc

theorem arbitrary_rearrangement_cannot_expose_private_input (a : Named Empty)
    (hs : Named.Structural hiddenSender a) (q : Named Empty) (m : Ground) :
    ¬ Named.FreeStep a (.input 7 m) q := by
  intro h
  have hc := h.channel_mem
  rw [← hs.channels,hidden_sender_has_no_free_channels] at hc
  exact Finset.notMem_empty _ hc

theorem alpha_renamed_private_output_stays_blocked (q : Named (Option Empty)) :
    Named.Structural hiddenSender
      (.newName (.channel 8) (.embed (.plain (.output 8 (.name 40) .nil)))) ∧
    ¬ Named.BoundOutput (.newName (.channel 8) (.embed (.plain (.output 8 (.name 40) .nil))) : Named Empty) 8 q := by
  constructor
  · simpa [hiddenSender,Named.mapNames,SourceName.map,Extended.mapNames,Agent.mapNames,Term.mapNames] using
      Named.Structural.alphaChannel (.embed (.plain (.output 7 (.name 40) .nil)) : Named Empty) 7 8 (by decide)
  · intro h
    have hc := h.channel_mem
    have hn : 8 ∉ (Named.newName (.channel 8) (.embed (.plain (.output 8 (.name 40) .nil))) : Named Empty).channels := by decide
    exact hn hc

/-- Dropping alpha freshness would change the set of free channels. -/
theorem capture_violates_free_channel_invariance :
    (({7,8} : Finset Nat).image (Equiv.swap 7 8)).erase 8 ≠ ({7,8} : Finset Nat).erase 7 := by decide

theorem public_secret_output_remains_possible :
    Named.BoundOutput
      (.newName (.channel 7) (.embed (.plain (.output 0 (.name 40) .nil))) : Named Empty) 0
      (.newName (.channel 7) (.embed (.par (.active none (.name 40)) (.plain .nil)))) :=
  .scopeName _ (by decide) (.embed (Extended.message_output _ _ _))

theorem private_internal_step_remains_possible :
    Named.Reduction privateExchange
      (.newName (.channel 7) (.embed (.plain (.par .nil (.output 0 (.name 40) .nil))))) :=
  SourceNameRestrictionSPOT.private_communication_inside_binder

theorem no_private_output_after_any_internal_execution (a : Named Empty)
    (ht : Relation.ReflTransGen Named.Reduction privateExchange a) (q : Named (Option Empty)) :
    ¬ Named.BoundOutput a 7 q := by
  intro h
  have hc := Named.reduction_star_channels_subset ht h.channel_mem
  have hn : 7 ∉ privateExchange.channels := by decide
  exact hn hc

/-- Inactive branches count in syntactic support and can disappear at Then.
Operational preservation is inclusion, not equality. -/
theorem conditional_can_remove_channels :
    Named.Reduction
      (.embed (.plain (.branch (.equal (.name 40) (.name 40)) .nil (.output 7 (.name 41) .nil))) : Named Empty)
      (.embed (.plain .nil)) ∧
    (Named.embed (.plain (.branch (.equal (.name 40) (.name 40)) .nil (.output 7 (.name 41) .nil))) : Named Empty).channels ≠
      (Named.embed (.plain .nil) : Named Empty).channels := by
  refine ⟨.embed (.thenBranch (.equal (.name 40) (.name 40)) .nil (.output 7 (.name 41) .nil) (.refl _)),?_⟩
  decide

/-- Full raw Rewrite changes base-name support but never channel support. -/
theorem base_support_is_not_the_channel_invariant :
    Named.Structural (.embed (.active (0 : Fin 1) (.name 40)))
      (.embed (.active 0 (.unary .fst (.binary .pair (.name 40) (.name 7))))) ∧
    (Named.embed (.active (0 : Fin 1) (.name 40))).freeNames ≠
      (Named.embed (.active (0 : Fin 1) (.unary .fst (.binary .pair (.name 40) (.name 7))))).freeNames ∧
    (Named.embed (.active (0 : Fin 1) (.name 40))).channels =
      (Named.embed (.active (0 : Fin 1) (.unary .fst (.binary .pair (.name 40) (.name 7))))).channels := by
  exact ⟨.embed (.rewrite 0 (EqE.equation (.fst (.name 40) (.name 7))).symm),by decide,rfl⟩

theorem actual_trustee_input_blocked (swap : Bool) (p : Process.Phase)
    (q : Named (Fin p.handles)) (r : Recipe p.handles) :
    ¬ Named.FreeStep
      (Named.restrictedState Channels.canonical.privateChannels
        (sourceState SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical p))
      (.input 1 r) q :=
  Named.restricted_private_free_blocked _ _ _ (Channels.trustee_private Channels.canonical)

theorem actual_honest_channel_after_internal_blocked (swap : Bool) (p : Process.Phase)
    (a : Named (Fin p.handles))
    (ht : Relation.ReflTransGen Named.Reduction
      (Named.restrictedState Channels.canonical.privateChannels
        (sourceState SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical p)) a)
    (q : Named (Option (Fin p.handles))) (i : Fin 2) :
    ¬ Named.BoundOutput a (Channels.canonical.voter i.val) q :=
  Named.after_internal_private_bound_blocked _ ht _ _ (Channels.honest_private Channels.canonical i)
end ExplainableCrypto.Helios.Symbolic.SourceChannelClosureSPOT
