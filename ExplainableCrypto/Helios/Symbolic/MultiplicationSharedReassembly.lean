import ExplainableCrypto.Helios.Symbolic.MultiplicationPieceReassembly

namespace ExplainableCrypto.Helios.Symbolic.Frame
variable {restricted : Finset Nat} {handles : Nat}

/-- Shared minimum pieces reassemble over any two frames when source minimum
competitors admit normal partitions. This uses the existing occurrence and
cost reassembly, without assuming destination normality or minimality. -/
theorem sharedMinimum_of_partition_shared_pieces_of_competitors (φ ψ : Frame restricted handles)
    (hcompetitors : ∀ m, MinimalRecipe restricted φ.value m →
      ∃ u, Irreducible u ∧ Nonempty (MultiplicationPartition restricted φ.value m u))
    (r : Recipe handles) {t : Ground}
    (p : MultiplicationPartition restricted φ.value r t) (ht : Irreducible t)
    (hpieces : ∀ x ∈ p.pieces, SharedMinimum φ ψ x.1) : SharedMinimum φ ψ r := by
  have hf : ∀ x ∈ p.pieces, x.2.mulFactors = {x.2.baseClass} := by
    intro x hx
    apply Term.mul_factor_singleton_of_mem (b := t)
    rw [← p.targetFactors]
    exact Multiset.mem_map.mpr ⟨x,hx,rfl⟩
  obtain ⟨r',s,u,p',q,hp',_,hs,hmin,hdest⟩ :=
    reassemble_minimum_pieces (τ := ψ.value) p.pieces p.pieces_ne_zero p.publicPieces p.values hf hpieces
  have htarget : BaseEq u t := by
    apply (baseEq_iff_mulFactors _ _).mpr
    rw [← p'.targetFactors,hp']
    exact p.targetFactors
  have hsource : BaseEq r r' := by
    apply (baseEq_iff_mulFactors _ _).mpr
    rw [← p'.sourceFactors,hp']
    exact p.sourceFactors.symm
  let q' := q.of_base htarget
  have hms := minimum_of_normal_partition_of_competitors hcompetitors s hs q' ht hmin
  exact ⟨s,hms,p.value.trans q'.value.symm,(hsource.sound.subst ψ.value).trans hdest⟩

end ExplainableCrypto.Helios.Symbolic.Frame

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Shared minima of all normal-partition pieces reassemble into a shared
globally minimum source recipe. Raw regrouping preserves the destination;
normal target factors and exact new budgets certify source minimality. -/
theorem sharedMinimum_of_partition_shared_pieces (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (ψ : Frame ns.restricted 3)
    (r : Recipe 3) {t : Ground}
    (p : MultiplicationPartition ns.restricted (frame ns swap left right).value r t)
    (ht : Irreducible t)
    (hpieces : ∀ x ∈ p.pieces, Frame.SharedMinimum (frame ns swap left right) ψ x.1) :
    Frame.SharedMinimum (frame ns swap left right) ψ r :=
  Frame.sharedMinimum_of_partition_shared_pieces_of_competitors _ ψ
    (fun m hm => normal_partition_of_minimum_mul_leaves ns swap left right ns.restricted m
      hm.isPublic (fun _ ha => hm.mul_leaf ha)) r p ht hpieces

/-- A non-ciphertext product with minimum children reduces shared minimization
to strictly smaller public recipes. The induction premise remains explicit;
there is no claim of unconditional multiplication transport here. -/
theorem minimum_children_non_ciphertext_mul_shared (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (ψ : Frame ns.restricted 3)
    (a b : Recipe 3)
    (ha : MinimalRecipe ns.restricted (frame ns swap left right).value a)
    (hb : MinimalRecipe ns.restricted (frame ns swap left right).value b)
    (hn : ¬ ((frame ns swap left right).eval (.binary .mul a b)).CiphertextValue)
    (hsmall : ∀ s : Recipe 3, s.Public ns.restricted → s.nodeCount < (Term.binary .mul a b).nodeCount →
      Frame.SharedMinimum (frame ns swap left right) ψ s) :
    Frame.SharedMinimum (frame ns swap left right) ψ (.binary .mul a b) := by
  obtain ⟨t,ht,⟨p⟩⟩ := normal_partition_of_minimum_mul_leaves ns swap left right ns.restricted
    (.binary .mul a b) ⟨ha.isPublic,hb.isPublic⟩ (by
      intro x hx
      rcases Multiset.mem_add.mp hx with hx | hx
      · exact ha.mul_leaf hx
      · exact hb.mul_leaf hx)
  rcases p.value.mul_irreducible_shape ht with ⟨x,y,rfl⟩ | ⟨k,nr,m,rfl⟩
  · apply sharedMinimum_of_partition_shared_pieces ns swap left right ψ _ p ht
    intro z hz
    have h := p.normal_product_pieces_smaller rfl z hz
    exact hsmall z.1 h.1 h.2
  · exact False.elim (hn ⟨k,nr,m,p.value⟩)

end ExplainableCrypto.Helios.Symbolic.Historical.General
