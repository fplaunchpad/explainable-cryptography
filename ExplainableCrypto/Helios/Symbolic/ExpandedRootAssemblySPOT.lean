import ExplainableCrypto.Helios.Symbolic.ExpandedRootAssembly
import ExplainableCrypto.Helios.Symbolic.ExpandedPairMinimumSPOT

namespace ExplainableCrypto.Helios.Symbolic.ExpandedRootAssemblySPOT
open Historical General

/-- Equal-candidate frames inhabit both successful-root transport premises by
actual minimum existence. The complete conditional pipeline yields all public
observations in expanded, partial and final presentations without assuming B8. -/
theorem conditional_pipeline_inhabited :
    let ns := LocalRootSPOT.names
    let left := LocalRootSPOT.left
    let φ := expandedFrame ns false left left []
    let ψ := expandedFrame ns true left left []
    Frame.DecryptCheckTransport φ ψ ∧ Frame.DecryptCheckTransport ψ φ ∧
      Frame.StaticEq φ ψ ∧
      Frame.StaticEq (partialFrame ns false left left []) (partialFrame ns true left left []) ∧
      Frame.StaticEq (finalFrame ns false left left []) (finalFrame ns true left left []) := by
  let ns := LocalRootSPOT.names
  let left := LocalRootSPOT.left
  let φ := expandedFrame ns false left left []
  let ψ := expandedFrame ns true left left []
  have h : Frame.DecryptCheckTransport φ ψ := by
    intro r hp _ _ _ _ _
    obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := φ.value) r hp
    exact ⟨m,hm,he,he⟩
  exact ⟨h,h,
    accepted_expanded_staticEq_of_decrypt_check_transport ns HistoricalFrameSPOT.fixture_names_fresh left left [] (by simp) trivial h h,
    accepted_partial_staticEq_of_decrypt_check_transport ns HistoricalFrameSPOT.fixture_names_fresh left left [] (by simp) trivial h h,
    accepted_final_staticEq_of_decrypt_check_transport ns HistoricalFrameSPOT.fixture_names_fresh left left [] (by simp) trivial h h⟩

end ExplainableCrypto.Helios.Symbolic.ExpandedRootAssemblySPOT
