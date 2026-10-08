import ExplainableCrypto.Helios.Symbolic.SourceFreshInputStates
import ExplainableCrypto.Helios.Symbolic.SourceInputAlphaBoundary
import ExplainableCrypto.Helios.Symbolic.SourceScopedSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceFreshNamesSPOT
open Historical General Source

theorem concrete_fresh_index :
    freshNameIndex ({.base 0,.channel 40} : Finset SourceName) = 41 ∧
    SourceName.base 41 ∉ ({.base 0,.channel 40} : Finset SourceName) ∧
    SourceName.channel 41 ∉ ({.base 0,.channel 40} : Finset SourceName) := by decide

theorem occupied_index_fails_freshness :
    SourceName.base 40 ∈ ({.base 40,.channel 7} : Finset SourceName) ∧
    SourceName.channel 7 ∈ ({.base 40,.channel 7} : Finset SourceName) := by decide

abbrev nested : Named (Fin 1) := .newName (.base 40)
  (.newVar (.newName (.channel 7)
    (.embed (.par (.active none (.binary .pair (.name 40) (.name 41)))
      (.plain (.input 0 (.output 0 (.var none) .nil)))))))

theorem bound_support_excludes_free_payload_names :
    nested.boundNames = {SourceName.base 40,SourceName.channel 7} ∧
    SourceName.base 41 ∉ nested.boundNames ∧ SourceName.base 41 ∈ nested.allNames := by decide

abbrev proofInput : Extended.FreeLabel (Fin 1) := .input 0
  (.spk (.name 40) (.name 42) (.const .one) (.binary .pair (.name 43) (.name 60)))

theorem fourth_field_is_in_avoidance : SourceName.base 60 ∈ proofInput.nameSupport := by decide

theorem nested_process_freshens_for_full_label :
    ∃ b : Named (Fin 1), Named.Structural nested b ∧
      (∀ n ∈ b.boundNames, n ∉ proofInput.nameSupport) ∧ b.channels = nested.channels := by
  obtain ⟨b,hs,hf⟩ := Named.exists_fresh_for_free_label nested proofInput
  exact ⟨b,hs,hf,hs.channels.symm⟩

theorem variable_renaming_keeps_name_binders :
    (nested.rename some).boundNames = {SourceName.base 40,SourceName.channel 7} := by
  rw [Named.boundNames_rename]
  exact bound_support_excludes_free_payload_names.1

theorem repeated_binders_can_be_fresh_and_distinct :
    ∃ (ns : List SourceName) (e k : Nat ≃ Nat),
      Named.Structural
        (Named.restrictNames [.base 40,.base 40] (.embed (SourceInputAlphaBoundary.keyAndInput 40)))
        (Named.restrictNames ns ((Named.embed (SourceInputAlphaBoundary.keyAndInput 40)).mapNames e k)) ∧
      ns.Nodup ∧ ns.length = 2 ∧ ∀ n ∈ ns, n ∉ ({.base 40} : Finset SourceName) := by
  obtain ⟨ns,e,k,ha,_,hf,hn,hl,_,_⟩ := Named.exists_common_fresh_prefix [.base 40,.base 40]
    (.embed (SourceInputAlphaBoundary.keyAndInput 40)) (.embed (SourceInputAlphaBoundary.keyAndInput 40)) {SourceName.base 40}
  exact ⟨ns,e,k,ha,hn,hl,hf⟩

abbrev receiving : ScopedState ({40} : Finset Nat) 1 :=
  ⟨SourceScopedSPOT.publicFrame,.input 0 (.output 0 (.var none) .nil)⟩

/-- A formerly bound literal can be used unchanged; the private key must
actually move and retains its full pk constructor at the same handle. -/
theorem old_literal_gets_fresh_policy_and_retained_key :
    ∃ e k : Nat ≃ Nat,
      Named.Structural (Named.restrictedState ({7} : Finset Nat) receiving)
        (Named.restrictedState (({7} : Finset Nat).image k) (receiving.mapNames e k)) ∧
      (Term.name 40 : Recipe 1).Public (({40} : Finset Nat).image e) ∧
      k 0 = 0 ∧ e 40 ≠ 40 ∧
      (receiving.frame.mapNames e).value 0 = .unary .pk (.name (e 40)) := by
  obtain ⟨e,k,hp,_,hr,hc,_⟩ := Named.exists_common_fresh_input_states (hidden := {7}) receiving receiving
    0 (.name 40) (by decide) (.refl _)
  refine ⟨e,k,hp,hr,hc,?_,rfl⟩
  intro he
  change 40 ∉ ({40} : Finset Nat).image e at hr
  exact hr (Finset.mem_image.mpr ⟨40,by simp,he⟩)

theorem public_label_literal_stays_fixed :
    ∃ e k : Nat ≃ Nat,
      Named.Structural (Named.restrictNames (Named.restrictionNames {7} {40}) (.embed (SourceInputAlphaBoundary.keyAndInput 40)))
        (Named.restrictNames (Named.restrictionNames (({7} : Finset Nat).image k) (({40} : Finset Nat).image e))
          ((Named.embed (SourceInputAlphaBoundary.keyAndInput 40)).mapNames e k)) ∧ e 41 = 41 := by
  obtain ⟨e,k,ha,_,_,hf⟩ := Named.exists_common_fresh_policy {7} {40}
    (.embed (SourceInputAlphaBoundary.keyAndInput 40)) (.embed (SourceInputAlphaBoundary.keyAndInput 40)) {SourceName.base 41}
  refine ⟨e,k,ha,?_⟩
  exact SourceName.base.inj (hf (.base 41) (by simp) (by simp [Named.base_mem_restrictionNames]))

/-- The retained alpha-boundary action still has precisely the same label and
target when its source is replaced by a fresh representative. -/
theorem prior_alpha_input_keeps_exact_action :
    ∃ a : Named (Fin 1),
      Named.Structural (.newName (.base 40) (.embed (SourceInputAlphaBoundary.keyAndInput 40))) a ∧
      (∀ n ∈ a.boundNames, n ∉ (Extended.FreeLabel.input 0 (.name 40) : Extended.FreeLabel (Fin 1)).nameSupport) ∧
      Named.FreeStep a (.input 0 (.name 40))
        (.newName (.base 41) (.embed (.par (.active (0 : Fin 1) (.unary .pk (.name 41)))
          (.plain (.output 0 (.name 40) .nil))))) :=
  SourceInputAlphaBoundary.old_literal_input_after_alpha.fresh_representative

theorem actual_two_worlds_freshen_arbitrary_input (p : Process.Phase)
    (h : Process.Reachable SharedTallySPOT.names false SharedTallySPOT.left SharedTallySPOT.right 1 p)
    (r : Recipe p.handles) :
    ∃ e k : Nat ≃ Nat,
      Named.Structural
        (Named.restrictedState Channels.canonical.privateChannels
          (sourceState SharedTallySPOT.names false SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical p))
        (Named.restrictedState (Channels.canonical.privateChannels.image k)
          ((sourceState SharedTallySPOT.names false SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical p).mapNames e k)) ∧
      Named.Structural
        (Named.restrictedState Channels.canonical.privateChannels
          (sourceState SharedTallySPOT.names true SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical p))
        (Named.restrictedState (Channels.canonical.privateChannels.image k)
          ((sourceState SharedTallySPOT.names true SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical p).mapNames e k)) ∧
      r.Public (SharedTallySPOT.names.restricted.image e) ∧ k 4 = 4 ∧
      ((sourceView SharedTallySPOT.names false SharedTallySPOT.left SharedTallySPOT.right p).mapNames e).StaticEq
        ((sourceView SharedTallySPOT.names true SharedTallySPOT.left SharedTallySPOT.right p).mapNames e) :=
  Named.exists_common_fresh_input_states _ _ 4 r (by decide)
    (reachable_source_view_staticEq NumericReflectionSPOT.fixture_names_fresh h)
end ExplainableCrypto.Helios.Symbolic.SourceFreshNamesSPOT
