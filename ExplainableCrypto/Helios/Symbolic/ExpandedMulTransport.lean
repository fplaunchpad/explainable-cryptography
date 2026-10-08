import ExplainableCrypto.Helios.Symbolic.ExpandedMulPartitions
import ExplainableCrypto.Helios.Symbolic.MultiplicationPartitionTransfer

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Complete non-ciphertext multiplication-valued equality branch for actual
accepted expanded frames. Normalization and ciphertext fusion preserve exact
public partitions, whose strictly smaller groups transfer and reassemble
whole-recipe equality. Destination minimality is not assumed. -/
theorem accepted_expanded_minimum_non_ciphertext_multiplication_equality_swap (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r s : Recipe (ExpandedHandles n))
    (hr : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (hs : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value s)
    {x y u v : Ground}
    (her : EqE ((expandedFrame ns swap left right rs).eval r) (.binary .mul x y))
    (hes : EqE ((expandedFrame ns swap left right rs).eval s) (.binary .mul u v))
    (hnr : ¬ ((expandedFrame ns swap left right rs).eval r).CiphertextValue)
    (hns : ¬ ((expandedFrame ns swap left right rs).eval s).CiphertextValue)
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow (expandedFrame ns swap' left right rs)
      (r.nodeCount+s.nodeCount)) :
    EqE ((expandedFrame ns swap left right rs).eval r) ((expandedFrame ns swap left right rs).eval s) ↔
      EqE ((expandedFrame ns swap' left right rs).eval r) ((expandedFrame ns swap' left right rs).eval s) := by
  have hn := accepted_expanded_results_numeric ns hf left right rs hp ha swap
  obtain ⟨a,b,rfl⟩ := expanded_minimum_non_ciphertext_mul_form ns swap left right rs hn ns.restricted r hr her hnr
  obtain ⟨c,d,rfl⟩ := expanded_minimum_non_ciphertext_mul_form ns swap left right rs hn ns.restricted s hs hes hns
  obtain ⟨⟨af,bf,hff,p,hpf⟩,⟨adest,bdest,hft,p',hpt⟩⟩ :=
    accepted_expanded_minimum_non_ciphertext_mul_partitions ns hf swap swap' left right rs hp ha a b hr hnr (hobs.mono (by omega))
  obtain ⟨⟨cf,df,hgf,q,hqf⟩,⟨ct,dt,hgt,q',hqt⟩⟩ :=
    accepted_expanded_minimum_non_ciphertext_mul_partitions ns hf swap swap' left right rs hp ha c d hs hns (hobs.mono (by omega))
  constructor
  · intro he
    apply p.transfer_normal_equality q hff hgf (expandedFrame ns swap' left right rs).value ?_ he
    intro x hx y hy hxy
    have hpx := hpf x hx
    have hqy := hqf y hy
    exact (hobs x.1 y.1 hpx.1 hqy.1 (by omega)).mp hxy
  · intro he
    apply p'.transfer_normal_equality q' hft hgt (expandedFrame ns swap left right rs).value ?_ he
    intro x hx y hy hxy
    have hpx := hpt x hx
    have hqy := hqt y hy
    exact (hobs x.1 y.1 hpx.1 hqy.1 (by omega)).mpr hxy

end ExplainableCrypto.Helios.Symbolic.Historical.General
