import ExplainableCrypto.Helios.Symbolic.MultiplicationSharedReassembly
import ExplainableCrypto.Helios.Symbolic.ExpandedMulOrigins
import ExplainableCrypto.Helios.Symbolic.BoundedSharedMinima

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Every source-minimum raw leaf has a single-factor normal representative.
The parent need not be minimum; numeric result origins suffice in this world. -/
theorem expanded_minimum_mul_leaf_normal_forms_source (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (r : Recipe (ExpandedHandles n))
    (hmin : ∀ a ∈ r.mulLeaves, MinimalRecipe restricted (expandedFrame ns swap left right rs).value a) :
    ∀ a ∈ r.mulLeaves, ∃ t, ReducesModulo ((expandedFrame ns swap left right rs).eval a) t ∧
      Irreducible t ∧ (∀ x y, t ≠ .binary .mul x y) := by
  intro a ha
  obtain ⟨t,ht,htn⟩ := exists_normal_form ((expandedFrame ns swap left right rs).eval a)
  refine ⟨t,ht.to_modulo,htn,?_⟩
  intro x y he
  subst t
  obtain ⟨u,v,hu⟩ := expanded_minimum_normal_mul_form ns swap left right rs hn restricted a (hmin a ha) htn ht.sound
  exact (Term.mulLeaves_mem ha).2 u v hu

/-- Minimum raw leaves yield a normal fusion partition even when the whole
product can shrink. Occurrence counts and source costs are exact. -/
theorem expanded_normal_partition_of_minimum_mul_leaves (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (r : Recipe (ExpandedHandles n)) (hp : r.Public restricted)
    (hmin : ∀ a ∈ r.mulLeaves, MinimalRecipe restricted (expandedFrame ns swap left right rs).value a) :
    ∃ t, Irreducible t ∧ Nonempty (MultiplicationPartition restricted (expandedFrame ns swap left right rs).value r t) :=
  exists_normal_recipe_partition restricted (expandedFrame ns swap left right rs).value r hp
    (expanded_minimum_mul_leaf_normal_forms_source ns swap left right rs hn restricted r hmin)

/-- Minimum partition pieces certify global minimum size against every public
competitor in the expanded source frame, under the caller's public policy. -/
theorem expanded_minimum_of_normal_partition (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (r : Recipe (ExpandedHandles n)) (hp : r.Public restricted) {t : Ground}
    (p : MultiplicationPartition restricted (expandedFrame ns swap left right rs).value r t)
    (ht : Irreducible t)
    (hmin : ∀ x ∈ p.pieces, MinimalRecipe restricted (expandedFrame ns swap left right rs).value x.1) :
    MinimalRecipe restricted (expandedFrame ns swap left right rs).value r :=
  minimum_of_normal_partition_of_competitors
    (fun m hm => expanded_normal_partition_of_minimum_mul_leaves ns swap left right rs hn restricted m
      hm.isPublic (fun _ ha => hm.mul_leaf ha)) r hp p ht hmin

/-- Two minimum groups remain minimum when their single-factor values form a
fully normal product. The normality premise excludes further ciphertext fusion. -/
theorem expanded_minimum_mul_of_normal_groups (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (a b : Recipe (ExpandedHandles n))
    (ha : MinimalRecipe restricted (expandedFrame ns swap left right rs).value a)
    (hb : MinimalRecipe restricted (expandedFrame ns swap left right rs).value b)
    {u v : Ground} (hea : EqE ((expandedFrame ns swap left right rs).eval a) u)
    (heb : EqE ((expandedFrame ns swap left right rs).eval b) v)
    (hu : u.mulFactors = {u.baseClass}) (hv : v.mulFactors = {v.baseClass})
    (ht : Irreducible (.binary .mul u v)) :
    MinimalRecipe restricted (expandedFrame ns swap left right rs).value (.binary .mul a b) := by
  let p := (MultiplicationPartition.single a u ha.isPublic hea hu).mul
    (MultiplicationPartition.single b v hb.isPublic heb hv)
  apply expanded_minimum_of_normal_partition ns swap left right rs hn restricted (.binary .mul a b)
    ⟨ha.isPublic,hb.isPublic⟩ p ht
  intro x hx
  simp only [p,MultiplicationPartition.mul,MultiplicationPartition.single,
    Multiset.mem_add,Multiset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ha
  · exact hb

/-- Existing shared reassembly applies to actual expanded partitions. Source
numeric origins discharge competitor partitions; destination frame values may
change and no destination normality or minimum premise is used. -/
theorem expanded_sharedMinimum_of_partition_shared_pieces (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (ψ : Frame ns.restricted (ExpandedHandles n))
    (r : Recipe (ExpandedHandles n)) {t : Ground}
    (p : MultiplicationPartition ns.restricted (expandedFrame ns swap left right rs).value r t)
    (ht : Irreducible t)
    (hpieces : ∀ x ∈ p.pieces, Frame.SharedMinimum (expandedFrame ns swap left right rs) ψ x.1) :
    Frame.SharedMinimum (expandedFrame ns swap left right rs) ψ r :=
  Frame.sharedMinimum_of_partition_shared_pieces_of_competitors _ ψ
    (fun m hm => expanded_normal_partition_of_minimum_mul_leaves ns swap left right rs hn ns.restricted m
      hm.isPublic (fun _ ha => hm.mul_leaf ha)) r p ht hpieces

/-- The complete non-ciphertext local multiplication case. Minimum children
supply source partitions; every surviving fusion group is strictly smaller
than the original product, so the induction premise supplies shared pieces. -/
theorem expanded_minimum_children_non_ciphertext_mul_shared (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (ψ : Frame ns.restricted (ExpandedHandles n))
    (a b : Recipe (ExpandedHandles n))
    (ha : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value a)
    (hb : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value b)
    (hnot : ¬ ((expandedFrame ns swap left right rs).eval (.binary .mul a b)).CiphertextValue)
    (hsmall : Frame.SharedMinimaBelow (expandedFrame ns swap left right rs) ψ (Term.binary .mul a b).nodeCount) :
    Frame.SharedMinimum (expandedFrame ns swap left right rs) ψ (.binary .mul a b) := by
  obtain ⟨t,ht,⟨p⟩⟩ := expanded_normal_partition_of_minimum_mul_leaves ns swap left right rs hn ns.restricted
    (.binary .mul a b) ⟨ha.isPublic,hb.isPublic⟩ (by
      intro x hx
      rcases Multiset.mem_add.mp hx with hx | hx
      · exact ha.mul_leaf hx
      · exact hb.mul_leaf hx)
  rcases p.value.mul_irreducible_shape ht with ⟨x,y,rfl⟩ | ⟨k,nr,m,rfl⟩
  · apply expanded_sharedMinimum_of_partition_shared_pieces ns swap left right rs hn ψ _ p ht
    intro z hz
    have h := p.normal_product_pieces_smaller rfl z hz
    exact hsmall z.1 h.1 h.2
  · exact False.elim (hnot ⟨k,nr,m,p.value⟩)

/-- Accepted publication discharges numeric origins. This branch needs only
forward smaller shared minima, not an observation or reverse-transport premise. -/
theorem accepted_expanded_minimum_children_non_ciphertext_mul_shared (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (a b : Recipe (ExpandedHandles n))
    (ha : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value a)
    (hb : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value b)
    (hnot : ¬ ((expandedFrame ns swap left right rs).eval (.binary .mul a b)).CiphertextValue)
    (hsmall : Frame.SharedMinimaBelow (expandedFrame ns swap left right rs)
      (expandedFrame ns swap' left right rs) (Term.binary .mul a b).nodeCount) :
    Frame.SharedMinimum (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs) (.binary .mul a b) :=
  expanded_minimum_children_non_ciphertext_mul_shared ns swap left right rs
    (accepted_expanded_results_numeric ns hf left right rs hp haccept swap) _ a b ha hb hnot hsmall

end ExplainableCrypto.Helios.Symbolic.Historical.General
