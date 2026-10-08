import ExplainableCrypto.Helios.Symbolic.SourceNamedPresentationNames
import ExplainableCrypto.Helios.Symbolic.SourceNamedStaticSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceNamedPermutationSPOT
open Historical General Source Extended
abbrev e : Nat ≃ Nat := Equiv.swap 40 50
abbrev k : Nat ≃ Nat := Equiv.swap 0 9

/-- The complete original alpha path, including its private bound name, moves
under the global permutation; the local alpha swap is conjugated. -/
theorem alpha_path_transported :
    Named.Structural
      ((Named.newName (.base 40) (.embed SourceNameInterpretationSPOT.binding)).mapNames e k)
      ((Named.newName (.base 50) (.embed (SourceNameInterpretationSPOT.binding.mapNames
        SourceNameInterpretationSPOT.e id))).mapNames e k) :=
  SourceNameInterpretationSPOT.alpha_binding_representative.mapNames e k

theorem fourth_field_swap_conjugated :
    ((Named.embed (.active (0 : Fin 1) SourceNamedStaticSPOT.fullTest)).mapNames (Equiv.swap 40 48) id).mapNames e k =
    ((Named.embed (.active (0 : Fin 1) SourceNamedStaticSPOT.fullTest)).mapNames e k).mapNames
      (Equiv.swap (e 40) (e 48)) id := Named.mapNames_base_swap _ e k 40 48

/-- Collapsing a free name onto a binder destroys free support: the image
formula for permutations is false for this noninjective map. -/
theorem collapsing_names_destroy_free_support :
    ((Named.newName (.base 40) (.embed (.active (0 : Fin 1) (.name 41)))).mapNames (fun _ => 0) id).freeNames ≠
      (Named.newName (.base 40) (.embed (.active (0 : Fin 1) (.name 41)))).freeNames.image
        (SourceName.map (fun _ => 0) id) := by decide

theorem collapsing_names_destroy_alpha_freshness :
    SourceName.base 50 ∉ (Named.embed (.active (0 : Fin 1) (.name 40))).allNames ∧
    SourceName.base 0 ∈ ((Named.embed (.active (0 : Fin 1) (.name 40))).mapNames (fun _ => 0) id).allNames := by decide

theorem alpha_input_keeps_consistently_mapped_label :
    Named.FreeStep (SourceOperationalPrenexSPOT.alphaSource.mapNames e k) (.input 9 (.name 50))
      (SourceOperationalPrenexSPOT.alphaTarget.mapNames e k) := by
  simpa only [FreeLabel.mapNames,Term.mapNames,Equiv.swap_apply_left] using
    SourceOperationalPrenexSPOT.alpha_input_reconstructed.mapNames e k

theorem stale_input_literal_rejected :
    (FreeLabel.input 0 (.name 40) : FreeLabel (Fin 1)).mapNames e k ≠ .input 9 (.name 40) := by
  simp [FreeLabel.mapNames,Term.mapNames,e,k]

theorem nested_bound_output_transported :
    Named.BoundOutput (SourceBoundPrenexSPOT.source.mapNames e k) 9 (SourceBoundPrenexSPOT.target.mapNames e k) := by
  simpa only [Equiv.swap_apply_left] using SourceBoundPrenexSPOT.scoped_bound_reconstructed.mapNames e k

theorem nested_bound_output_reflected :
    Named.BoundOutput SourceBoundPrenexSPOT.source 0 SourceBoundPrenexSPOT.target :=
  (Named.BoundOutput.mapNames_iff _ _ 0 e k).mp nested_bound_output_transported

theorem full_presentation_values_and_policy_move :
    ((Named.restrictedState ∅ SourceNamedStaticSPOT.p).mapNames e k).RepresentsFrame
      ((∅ : Finset Nat).image k) (SourceAtomicOutputSPOT.oldFrame.mapNames e) ∧
    (SourceAtomicOutputSPOT.oldFrame.mapNames e).value 0 = .unary .pk (.name 50) ∧
    ({40} : Finset Nat).image e = {50} :=
  ⟨(Named.restrictedState_represents SourceNamedStaticSPOT.p).mapNames e k,by decide,by decide⟩

theorem stale_private_policy_rejected : ({40} : Finset Nat).image e ≠ {40} := by decide

theorem full_named_static_witness_preserved_and_reflected :
    Named.StaticEq
      ((Named.restrictedState ∅ SourceNamedStaticSPOT.p).mapNames e k)
      ((Named.restrictedState ∅ SourceNamedStaticSPOT.p).mapNames e k) ∧
    (Named.StaticEq
      ((Named.restrictedState ∅ SourceNamedStaticSPOT.p).mapNames e k)
      ((Named.restrictedState ∅ SourceNamedStaticSPOT.p).mapNames e k) ↔
      Named.StaticEq (Named.restrictedState ∅ SourceNamedStaticSPOT.p) (Named.restrictedState ∅ SourceNamedStaticSPOT.p)) :=
  ⟨SourceNamedStaticSPOT.actual_restricted_frame_reflexive.mapNames e k,Named.staticEq_mapNames_iff _ _ e k⟩

theorem moved_private_channel_still_blocked (b : Named (Option (Fin 1))) :
    ¬ Named.BoundOutput ((Named.newName (.channel 0) SourceBoundPrenexSPOT.source).mapNames e k) 9 b := by
  intro h
  have he := h.channel_mem
  simp only [Named.mapNames,SourceName.map,Named.channels,Equiv.swap_apply_left,Finset.notMem_erase] at he

theorem actual_private_communication_transported :
    Named.Reduction (SourceOperationalPrenexSPOT.beforeNamed.mapNames e k)
      (SourceOperationalPrenexSPOT.afterNamed.mapNames e k) :=
  SourceOperationalPrenexSPOT.private_internal_reconstructed.mapNames e k

end ExplainableCrypto.Helios.Symbolic.SourceNamedPermutationSPOT
