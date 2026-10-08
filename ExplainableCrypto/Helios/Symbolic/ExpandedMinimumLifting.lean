import ExplainableCrypto.Helios.Symbolic.ExpandedObservationAssembly
import ExplainableCrypto.Helios.Symbolic.BoundedSharedMinima

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Reverse shared minimization supplies destination minima for the assembled
expanded observation step. The shared-minimum premise is still unproved. -/
theorem accepted_expanded_minimum_observation_step_of_reverse_minima (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (hreverse : Frame.CommonMinima (expandedFrame ns true left right rs) (expandedFrame ns false left right rs)) :
    Frame.MinimumObservationStep (expandedFrame ns false left right rs) (expandedFrame ns true left right rs) := by
  intro r s hr hs hobs
  exact accepted_expanded_minimum_equality_swap_of_both_minima ns hf left right rs hp ha r s hr hs
    (hreverse.minimum_destination hr) (hreverse.minimum_destination hs) hobs

/-- Two-way shared minima are exactly the remaining expanded static-equivalence
obligation. The theorem proves neither transport premise on its own. -/
theorem accepted_expanded_staticEq_iff_common_minima (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs) :
    Frame.StaticEq (expandedFrame ns false left right rs) (expandedFrame ns true left right rs) ↔
      Frame.CommonMinima (expandedFrame ns false left right rs) (expandedFrame ns true left right rs) ∧
      Frame.CommonMinima (expandedFrame ns true left right rs) (expandedFrame ns false left right rs) := by
  constructor
  · intro h
    exact ⟨h.common_minima,h.symm.common_minima⟩
  · rintro ⟨hforward,hreverse⟩
    exact Frame.staticEq_of_common_minima hforward
      (accepted_expanded_minimum_observation_step_of_reverse_minima ns hf left right rs hp ha hreverse)

/-- Exact tuple/individual presentation transfer carries the remaining
transport obligation to the actual final transcript. -/
theorem accepted_final_staticEq_iff_expanded_common_minima (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs) :
    Frame.StaticEq (finalFrame ns false left right rs) (finalFrame ns true left right rs) ↔
      Frame.CommonMinima (expandedFrame ns false left right rs) (expandedFrame ns true left right rs) ∧
      Frame.CommonMinima (expandedFrame ns true left right rs) (expandedFrame ns false left right rs) :=
  (expanded_frame_staticEq_iff_final ns left right rs).symm.trans
    (accepted_expanded_staticEq_iff_common_minima ns hf left right rs hp ha)

/-- Result publication is public postprocessing; the aggregate-partial target
has the same exact remaining two-way shared-minimum obligation. -/
theorem accepted_partial_staticEq_iff_expanded_common_minima (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs) :
    Frame.StaticEq (partialFrame ns false left right rs) (partialFrame ns true left right rs) ↔
      Frame.CommonMinima (expandedFrame ns false left right rs) (expandedFrame ns true left right rs) ∧
      Frame.CommonMinima (expandedFrame ns true left right rs) (expandedFrame ns false left right rs) :=
  (expanded_frame_staticEq_iff_partial ns left right rs hp).symm.trans
    (accepted_expanded_staticEq_iff_common_minima ns hf left right rs hp ha)

/-- Local source-minimum representatives in both directions suffice for the
actual expanded static-equivalence target, with no observation premise left. -/
theorem accepted_expanded_staticEq_of_local_transport_both (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (hforward : Frame.LocalMinimumTransport (expandedFrame ns false left right rs) (expandedFrame ns true left right rs))
    (hreverse : Frame.LocalMinimumTransport (expandedFrame ns true left right rs) (expandedFrame ns false left right rs)) :
    Frame.StaticEq (expandedFrame ns false left right rs) (expandedFrame ns true left right rs) :=
  (accepted_expanded_staticEq_iff_common_minima ns hf left right rs hp ha).mpr
    ⟨Frame.common_minima_of_local hforward,Frame.common_minima_of_local hreverse⟩

/-- The simultaneous transport induction can obtain every smaller observation
from the same strict bound in both directions. All value branches and reversed
acceptance are now discharged by the expanded observation assembly. -/
theorem accepted_expanded_observationsBelow_of_two_way_minima (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs) (bound : Nat)
    (hforward : Frame.SharedMinimaBelow (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs) bound)
    (hreverse : Frame.SharedMinimaBelow (expandedFrame ns swap' left right rs) (expandedFrame ns swap left right rs) bound) :
    Frame.ObservationsBelow (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs) bound := by
  cases swap <;> cases swap'
  · intro r s _ _ _; exact Iff.rfl
  · exact Frame.observationsBelow_of_shared_minima hforward hreverse
      (accepted_expanded_minimum_equality_swap_of_both_minima ns hf left right rs hp ha)
  · exact Frame.observationsBelow_of_shared_minima hforward hreverse
      (accepted_expanded_minimum_equality_swap_of_both_minima ns hf right left rs hp
        (accepted_sequence_reversed_candidates ns hf left right rs hp ha))
  · intro r s _ _ _; exact Iff.rfl

end ExplainableCrypto.Helios.Symbolic.Historical.General
