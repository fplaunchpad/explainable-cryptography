import ExplainableCrypto.Helios.Symbolic.DecryptCheckMulTransport

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type} {restricted : Finset Nat} {σ : V → Term W}

/-- Every raw product leaf inherits minimum size through its syntax context. -/
theorem MinimalRecipe.mul_leaf {r a : Term V} (hm : MinimalRecipe restricted σ r)
    (ha : a ∈ r.mulLeaves) : MinimalRecipe restricted σ a := by
  obtain ⟨⟨c,hc⟩,_⟩ := Term.mulLeaves_mem ha
  rw [← hc] at hm
  exact hm.subterm c

/-- Equal normal endpoints match every piece occurrence. Minimum source
pieces bound the competitor's public piece costs without assuming its pieces
minimum. The exact partition budgets recover the whole-recipe inequality. -/
theorem MultiplicationPartition.minimum_pieces_cost_le {r s : Term V} {a b : Term W}
    (p : MultiplicationPartition restricted σ r a) (q : MultiplicationPartition restricted σ s b)
    (ha : Irreducible a) (hb : Irreducible b)
    (hmin : ∀ x ∈ p.pieces, MinimalRecipe restricted σ x.1)
    (he : EqE (r.subst σ) (s.subst σ)) : r.nodeCount ≤ s.nodeCount := by
  have he' := (irreducible_eqE_iff_base ha hb).mp (p.value.symm.trans (he.trans q.value))
  have hbag := p.targetFactors.trans (he'.mul_factors.trans q.targetFactors.symm)
  have hrel : Multiset.Rel (fun x y : Term V × Term W => x.2.baseClass = y.2.baseClass)
      p.pieces q.pieces := by
    rw [← Multiset.rel_map,Multiset.rel_eq]
    exact hbag
  have hcost : Multiset.Rel (· ≤ ·) (p.pieces.map (fun x => x.1.nodeCount+1))
      (q.pieces.map (fun x => x.1.nodeCount+1)) := by
    rw [Multiset.rel_map]
    exact hrel.mono (fun x hx y hy hxy => Nat.add_le_add_right
      ((hmin x hx).least y.1 (q.publicPieces y hy)
        ((p.values x hx).trans (((baseClass_eq_iff _ _).mp hxy).sound.trans (q.values y hy).symm))) 1)
  have hc : (p.pieces.map (fun x => x.1.nodeCount+1)).sum ≤
      (q.pieces.map (fun x => x.1.nodeCount+1)).sum := by
    have sum_le {xs ys : Multiset Nat} (h : Multiset.Rel (· ≤ ·) xs ys) : xs.sum ≤ ys.sum := by
      induction h with
      | zero => exact Nat.le_refl _
      | cons h _ ih => simp only [Multiset.sum_cons]; omega
    exact sum_le hcost
  rw [p.budget,q.budget] at hc
  omega

/-- A normal partition certifies global minimum size when minimum competitors
also admit normal partitions. The source-specific origin proof is supplied
separately; comparison and exact occurrence costs are shared. -/
theorem minimum_of_normal_partition_of_competitors
    (hcompetitors : ∀ m, MinimalRecipe restricted σ m →
      ∃ u, Irreducible u ∧ Nonempty (MultiplicationPartition restricted σ m u))
    (r : Term V) (hp : r.Public restricted) {t : Term W}
    (p : MultiplicationPartition restricted σ r t) (ht : Irreducible t)
    (hmin : ∀ x ∈ p.pieces, MinimalRecipe restricted σ x.1) :
    MinimalRecipe restricted σ r := by
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := σ) r hp
  obtain ⟨u,hu,⟨q⟩⟩ := hcompetitors m hm
  exact hm.of_equivalent_size hp he (p.minimum_pieces_cost_le q ht hu hmin he)

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Source minimum leaves have single-factor normal representatives under
any caller policy. Ciphertext factors are allowed; no observation premise is
needed to establish this one-world fact. -/
theorem minimum_mul_leaf_normal_forms_source (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hmin : ∀ a ∈ r.mulLeaves, MinimalRecipe restricted (frame ns swap left right).value a) :
    ∀ a ∈ r.mulLeaves, ∃ t, ReducesModulo ((frame ns swap left right).eval a) t ∧
      Irreducible t ∧ (∀ x y, t ≠ .binary .mul x y) := by
  intro a ha
  obtain ⟨t,ht,hn⟩ := exists_normal_form ((frame ns swap left right).eval a)
  refine ⟨t,ht.to_modulo,hn,?_⟩
  intro x y he
  subst t
  obtain ⟨u,v,hu⟩ := minimum_normal_mul_form ns swap left right restricted a (hmin a ha) hn ht.sound
  exact (Term.mulLeaves_mem ha).2 u v hu

/-- Normalize minimum raw leaves and retain all fusion groups with exact
recipe costs. The source recipe itself need not be minimum. -/
theorem normal_partition_of_minimum_mul_leaves (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hp : r.Public restricted)
    (hmin : ∀ a ∈ r.mulLeaves, MinimalRecipe restricted (frame ns swap left right).value a) :
    ∃ t, Irreducible t ∧ Nonempty (MultiplicationPartition restricted (frame ns swap left right).value r t) :=
  exists_normal_recipe_partition restricted (frame ns swap left right).value r hp
    (minimum_mul_leaf_normal_forms_source ns swap left right restricted r hmin)

/-- A normal partition with globally minimum piece recipes certifies global
minimum size of the original recipe in the initial historical frame. -/
theorem minimum_of_normal_partition (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hp : r.Public restricted) {t : Ground}
    (p : MultiplicationPartition restricted (frame ns swap left right).value r t)
    (ht : Irreducible t)
    (hmin : ∀ x ∈ p.pieces, MinimalRecipe restricted (frame ns swap left right).value x.1) :
    MinimalRecipe restricted (frame ns swap left right).value r :=
  minimum_of_normal_partition_of_competitors
    (fun m hm => normal_partition_of_minimum_mul_leaves ns swap left right restricted m
      hm.isPublic (fun _ ha => hm.mul_leaf ha)) r hp p ht hmin

end ExplainableCrypto.Helios.Symbolic.Historical.General
