import ExplainableCrypto.Helios.Symbolic.MultiplicationLeaves

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type} {restricted : Finset Nat} {σ : V → Term W}

/-- Combine two partitions without grouping or dropping any occurrences. -/
def MultiplicationPartition.mul {r s : Term V} {a b : Term W}
    (p : MultiplicationPartition restricted σ r a) (q : MultiplicationPartition restricted σ s b) :
    MultiplicationPartition restricted σ (.binary .mul r s) (.binary .mul a b) where
  pieces := p.pieces + q.pieces
  sourceFactors := by simp only [Multiset.map_add, Multiset.sum_add, p.sourceFactors, q.sourceFactors, Term.mulFactors]
  targetFactors := by simp only [Multiset.map_add, p.targetFactors, q.targetFactors, Term.mulFactors]
  values := by
    intro x hx
    exact (Multiset.mem_add.mp hx).elim (p.values x) (q.values x)
  publicPieces := by
    intro x hx
    exact (Multiset.mem_add.mp hx).elim (p.publicPieces x) (q.publicPieces x)
  budget := by
    simp only [Multiset.map_add, Multiset.sum_add, p.budget, q.budget, Term.nodeCount]
    omega
  value := .binary .mul p.value q.value

private theorem singleton_factors {t : Term W} (h : ∀ x y, t ≠ .binary .mul x y) :
    t.mulFactors = {t.baseClass} := by
  cases t with
  | binary f x y => cases f <;> first | rfl | exact False.elim (h x y rfl)
  | _ => rfl

private theorem singleton_partition (r : Term V) (hp : r.Public restricted)
    (hs : r.mulLeaves = {r})
    (h : ∀ a ∈ r.mulLeaves, ∃ t, ReducesModulo (a.subst σ) t ∧ Irreducible t ∧
      (∀ x y, t ≠ .binary .mul x y)) :
    ∃ t, t.NormalMulFactors ∧ Nonempty (MultiplicationPartition restricted σ r t) := by
  obtain ⟨t, ht, hn, hhead⟩ := h r (by rw [hs]; simp)
  refine ⟨t, hn.normal_mul_factors, ⟨{
    pieces := {(r,t)}
    sourceFactors := by simp
    targetFactors := ?_
    values := ?_
    publicPieces := ?_
    budget := by simp
    value := ht.sound
  }⟩⟩
  · simpa using (singleton_factors hhead).symm
  · intro q hq
    have he := Multiset.mem_singleton.mp hq
    subst q
    exact ht.sound
  · intro q hq
    have he := Multiset.mem_singleton.mp hq
    subst q
    exact hp

/-- Normalize each raw outer leaf independently while retaining its public
recipe. The resulting product has normal factors but may still admit fusion. -/
theorem exists_normal_factor_partition (restricted : Finset Nat) (σ : V → Term W)
    (r : Term V) (hp : r.Public restricted)
    (h : ∀ a ∈ r.mulLeaves, ∃ t, ReducesModulo (a.subst σ) t ∧ Irreducible t ∧
      (∀ x y, t ≠ .binary .mul x y)) :
    ∃ t, t.NormalMulFactors ∧ Nonempty (MultiplicationPartition restricted σ r t) := by
  induction r with
  | binary f a b ia ib =>
    cases f with
    | mul =>
      obtain ⟨u, hu, ⟨p⟩⟩ := ia hp.1 (fun x hx => h x (Multiset.mem_add.mpr (Or.inl hx)))
      obtain ⟨v, hv, ⟨q⟩⟩ := ib hp.2 (fun x hx => h x (Multiset.mem_add.mpr (Or.inr hx)))
      refine ⟨.binary .mul u v, ?_, ⟨p.mul q⟩⟩
      intro x hx
      exact (Multiset.mem_add.mp hx).elim (hu x) (hv x)
    | pair | compose | add | partialDecrypt | dec => exact singleton_partition _ hp rfl h
  | _ => exact singleton_partition _ hp rfl h

/-- After leaf normalization, actual fusion paths produce a fully normal
endpoint with an exact public recipe partition and the original size budget. -/
theorem exists_normal_recipe_partition (restricted : Finset Nat) (σ : V → Term W)
    (r : Term V) (hp : r.Public restricted)
    (h : ∀ a ∈ r.mulLeaves, ∃ t, ReducesModulo (a.subst σ) t ∧ Irreducible t ∧
      (∀ x y, t ≠ .binary .mul x y)) :
    ∃ t, Irreducible t ∧ Nonempty (MultiplicationPartition restricted σ r t) := by
  obtain ⟨u, hu, ⟨p⟩⟩ := exists_normal_factor_partition restricted σ r hp h
  obtain ⟨t, ht, hn⟩ := exists_normal_form u
  exact ⟨t, hn, p.reduces hu ht.to_modulo⟩

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Every source minimum derives public normal-form partitions in both worlds.
The non-mul leaf condition follows from minimum origins, not a caller premise. -/
theorem minimum_normal_partitions (ns : Names n)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right) r.nodeCount) :
    (∃ t, Irreducible t ∧ Nonempty (MultiplicationPartition ns.restricted (frame ns false left right).value r t)) ∧
    (∃ t, Irreducible t ∧ Nonempty (MultiplicationPartition ns.restricted (frame ns true left right).value r t)) := by
  have h := minimum_mul_leaf_normal_forms ns left right r hm hobs
  exact ⟨exists_normal_recipe_partition _ _ r hm.isPublic h.1,
    exists_normal_recipe_partition _ _ r hm.isPublic h.2⟩

/-- A non-ciphertext minimum product has multiplication normal forms in both
worlds, with every retained fusion group represented by a strictly smaller
public recipe. Source size and publicness, rather than destination minimality,
supply the comparison budgets. -/
theorem minimum_non_ciphertext_mul_partitions (ns : Names n)
    (left right : CandidateSubstitution n Empty) (a b : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns false left right).value (.binary .mul a b))
    (hn : ¬ ((frame ns false left right).eval (.binary .mul a b)).CiphertextValue)
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      (Term.binary .mul a b).nodeCount) :
    (∃ x y, Irreducible (.binary .mul x y) ∧
      ∃ p : MultiplicationPartition ns.restricted (frame ns false left right).value (.binary .mul a b) (.binary .mul x y),
        ∀ q ∈ p.pieces, q.1.Public ns.restricted ∧ q.1.nodeCount < (Term.binary .mul a b).nodeCount) ∧
    (∃ x y, Irreducible (.binary .mul x y) ∧
      ∃ p : MultiplicationPartition ns.restricted (frame ns true left right).value (.binary .mul a b) (.binary .mul x y),
        ∀ q ∈ p.pieces, q.1.Public ns.restricted ∧ q.1.nodeCount < (Term.binary .mul a b).nodeCount) := by
  have hd : ¬ ((frame ns true left right).eval (.binary .mul a b)).CiphertextValue :=
    fun h => hn ((minimum_value_shape_reflection ns left right _ hm hobs).2.1 h)
  obtain ⟨⟨u, hu, ⟨p⟩⟩, ⟨v, hv, ⟨q⟩⟩⟩ := minimum_normal_partitions ns left right _ hm hobs
  constructor
  · rcases p.value.mul_irreducible_shape hu with ⟨x, y, rfl⟩ | ⟨k, r, m, rfl⟩
    · exact ⟨x, y, hu, p, fun z hz => p.normal_product_pieces_smaller rfl z hz⟩
    · exact False.elim (hn ⟨k, r, m, p.value⟩)
  · rcases q.value.mul_irreducible_shape hv with ⟨x, y, rfl⟩ | ⟨k, r, m, rfl⟩
    · exact ⟨x, y, hv, q, fun z hz => q.normal_product_pieces_smaller rfl z hz⟩
    · exact False.elim (hd ⟨k, r, m, q.value⟩)

end ExplainableCrypto.Helios.Symbolic.Historical.General
