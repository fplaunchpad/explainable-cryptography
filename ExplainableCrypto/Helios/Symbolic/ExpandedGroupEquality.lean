import ExplainableCrypto.Helios.Symbolic.ProtectedGroupEquality
import ExplainableCrypto.Helios.Symbolic.ExpandedFrameEquivalence

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Actual public submissions give the opaque protection needed for all nine
expanded group comparisons. Acceptance is unnecessary for this classification. -/
theorem expanded_group_components_eq_iff (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (a b : CiphertextGroup n (ExpandedHandles n))
    (ha : a.Public ns.restricted) (hb : b.Public ns.restricted) :
    (EqE (a.nonce ns (expandedFrame ns swap left right rs)) (b.nonce ns (expandedFrame ns swap left right rs)) ∧
      EqE (a.message (expandedFrame ns swap left right rs) swap left right)
        (b.message (expandedFrame ns swap left right rs) swap left right)) ↔
    CiphertextGroup.Observation (expandedFrame ns swap left right rs) a b :=
  CiphertextGroup.components_eq_iff_of_opaque_protected ns hf _
    (expanded_frame_opaque_protected ns swap left right rs hp)
    (fun i => Finset.mem_union_right _ (ns.nonce_mem_nonceNames i.1 i.2)) swap left right a b ha hb

/-- Exact grouped ciphertext equality retains the separate key comparison. -/
theorem expanded_group_ciphertext_eq_iff (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (a b : CiphertextGroup n (ExpandedHandles n))
    (ha : a.Public ns.restricted) (hb : b.Public ns.restricted) (k l : Ground) :
    EqE (.ternary .penc k (a.nonce ns (expandedFrame ns swap left right rs))
        (a.message (expandedFrame ns swap left right rs) swap left right))
      (.ternary .penc l (b.nonce ns (expandedFrame ns swap left right rs))
        (b.message (expandedFrame ns swap left right rs) swap left right)) ↔
    EqE k l ∧ CiphertextGroup.Observation (expandedFrame ns swap left right rs) a b :=
  (EqE.penc_iff _ _ _ _ _ _).trans
    (and_congr Iff.rfl (expanded_group_components_eq_iff ns hf swap left right rs hp a b ha hb))

/-- Group component equality transfers using strictly smaller public tests.
The group-size bounds must still be connected to the original assemblies. -/
theorem expanded_group_components_equality_swap (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (a b : CiphertextGroup n (ExpandedHandles n))
    (ha : a.Public ns.restricted) (hb : b.Public ns.restricted)
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow (expandedFrame ns swap' left right rs)
      (a.budget+b.budget)) :
    (EqE (a.nonce ns (expandedFrame ns swap left right rs)) (b.nonce ns (expandedFrame ns swap left right rs)) ∧
      EqE (a.message (expandedFrame ns swap left right rs) swap left right)
        (b.message (expandedFrame ns swap left right rs) swap left right)) ↔
    (EqE (a.nonce ns (expandedFrame ns swap' left right rs)) (b.nonce ns (expandedFrame ns swap' left right rs)) ∧
      EqE (a.message (expandedFrame ns swap' left right rs) swap' left right)
        (b.message (expandedFrame ns swap' left right rs) swap' left right)) :=
  (expanded_group_components_eq_iff ns hf swap left right rs hp a b ha hb).trans
    ((CiphertextGroup.observation_transfer_of_group_bounds _ _ a b ha hb hobs).trans
      (expanded_group_components_eq_iff ns hf swap' left right rs hp a b ha hb).symm)

end ExplainableCrypto.Helios.Symbolic.Historical.General
