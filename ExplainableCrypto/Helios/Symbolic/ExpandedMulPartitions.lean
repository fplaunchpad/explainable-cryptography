import ExplainableCrypto.Helios.Symbolic.ExpandedMulOrigins
import ExplainableCrypto.Helios.Symbolic.MinimumMultiplicationPartitions

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Every non-mul raw leaf of a source minimum normalizes to a single factor in
both worlds. Ciphertext factors remain allowed and may fuse with other factors. -/
theorem accepted_expanded_minimum_mul_leaf_normal_forms (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow (expandedFrame ns swap' left right rs) r.nodeCount) :
    (∀ a ∈ r.mulLeaves, ∃ t, ReducesModulo ((expandedFrame ns swap left right rs).eval a) t ∧
      Irreducible t ∧ (∀ x y, t ≠ .binary .mul x y)) ∧
    (∀ a ∈ r.mulLeaves, ∃ t, ReducesModulo ((expandedFrame ns swap' left right rs).eval a) t ∧
      Irreducible t ∧ (∀ x y, t ≠ .binary .mul x y)) := by
  have info {a : Recipe (ExpandedHandles n)} (ha : a ∈ r.mulLeaves) :
      MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value a ∧
      a.nodeCount ≤ r.nodeCount ∧ (∀ x y, a ≠ .binary .mul x y) := by
    obtain ⟨⟨c,hc⟩,hn⟩ := Term.mulLeaves_mem ha
    have hmc := hm
    rw [← hc] at hmc
    exact ⟨hmc.subterm c,by simpa only [hc] using c.nodeCount_hole_le a,hn⟩
  constructor
  · intro a hleaf
    have hi := info hleaf
    obtain ⟨t,ht,hn⟩ := exists_normal_form ((expandedFrame ns swap left right rs).eval a)
    refine ⟨t,ht.to_modulo,hn,?_⟩
    intro x y he
    subst t
    obtain ⟨u,v,huv⟩ := expanded_minimum_normal_mul_form ns swap left right rs
      (accepted_expanded_results_numeric ns hf left right rs hp ha swap) ns.restricted a hi.1 hn ht.sound
    exact hi.2.2 u v huv
  · intro a hleaf
    have hi := info hleaf
    obtain ⟨t,ht,hn⟩ := exists_normal_form ((expandedFrame ns swap' left right rs).eval a)
    refine ⟨t,ht.to_modulo,hn,?_⟩
    intro x y he
    subst t
    obtain ⟨u,v,huv⟩ := accepted_expanded_minimum_normal_mul_form_after_swap ns hf swap swap' left right rs hp ha a hi.1
      (hobs.mono hi.2.1) hn ht.sound
    exact hi.2.2 u v huv

/-- Actual fusion partitions exist in both expanded worlds, preserving all
source occurrences, publicness and the original recipe-size accounting. -/
theorem accepted_expanded_minimum_normal_partitions (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow (expandedFrame ns swap' left right rs) r.nodeCount) :
    (∃ t, Irreducible t ∧ Nonempty (MultiplicationPartition ns.restricted (expandedFrame ns swap left right rs).value r t)) ∧
    (∃ t, Irreducible t ∧ Nonempty (MultiplicationPartition ns.restricted (expandedFrame ns swap' left right rs).value r t)) := by
  have h := accepted_expanded_minimum_mul_leaf_normal_forms ns hf swap swap' left right rs hp ha r hm hobs
  exact ⟨exists_normal_recipe_partition _ _ r hm.isPublic h.1,exists_normal_recipe_partition _ _ r hm.isPublic h.2⟩

/-- Non-ciphertext minimum products retain normal product endpoints in both
worlds. Each fully fused group still has a strictly smaller public recipe. -/
theorem accepted_expanded_minimum_non_ciphertext_mul_partitions (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (a b : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (.binary .mul a b))
    (hn : ¬ ((expandedFrame ns swap left right rs).eval (.binary .mul a b)).CiphertextValue)
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow (expandedFrame ns swap' left right rs)
      (Term.binary .mul a b).nodeCount) :
    (∃ x y, Irreducible (.binary .mul x y) ∧
      ∃ p : MultiplicationPartition ns.restricted (expandedFrame ns swap left right rs).value (.binary .mul a b) (.binary .mul x y),
        ∀ q ∈ p.pieces, q.1.Public ns.restricted ∧ q.1.nodeCount < (Term.binary .mul a b).nodeCount) ∧
    (∃ x y, Irreducible (.binary .mul x y) ∧
      ∃ p : MultiplicationPartition ns.restricted (expandedFrame ns swap' left right rs).value (.binary .mul a b) (.binary .mul x y),
        ∀ q ∈ p.pieces, q.1.Public ns.restricted ∧ q.1.nodeCount < (Term.binary .mul a b).nodeCount) := by
  have hd : ¬ ((expandedFrame ns swap' left right rs).eval (.binary .mul a b)).CiphertextValue :=
    fun h => hn ((accepted_expanded_minimum_value_shapes_swap ns hf swap swap' left right rs hp ha _ hm hobs).2.1.mpr h)
  obtain ⟨⟨u,hu,⟨p⟩⟩,⟨v,hv,⟨q⟩⟩⟩ := accepted_expanded_minimum_normal_partitions ns hf swap swap' left right rs hp ha _ hm hobs
  constructor
  · rcases p.value.mul_irreducible_shape hu with ⟨x,y,rfl⟩ | ⟨k,r,m,rfl⟩
    · exact ⟨x,y,hu,p,fun z hz => p.normal_product_pieces_smaller rfl z hz⟩
    · exact False.elim (hn ⟨k,r,m,p.value⟩)
  · rcases q.value.mul_irreducible_shape hv with ⟨x,y,rfl⟩ | ⟨k,r,m,rfl⟩
    · exact ⟨x,y,hv,q,fun z hz => q.normal_product_pieces_smaller rfl z hz⟩
    · exact False.elim (hd ⟨k,r,m,q.value⟩)

end ExplainableCrypto.Helios.Symbolic.Historical.General
