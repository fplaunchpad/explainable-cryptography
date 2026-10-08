import ExplainableCrypto.Helios.Symbolic.NormalMultiplicationFactors

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type}

/-- A partition retains public recipe occurrences, evaluated factor values,
exact source/target factor bags, and the original raw node-count budget. -/
structure MultiplicationPartition (restricted : Finset Nat) (σ : V → Term W)
    (source : Term V) (target : Term W) where
  pieces : Multiset (Term V × Term W)
  sourceFactors : (pieces.map (fun p => p.1.mulFactors)).sum = source.mulFactors
  targetFactors : pieces.map (fun p => p.2.baseClass) = target.mulFactors
  values : ∀ p ∈ pieces, EqE (p.1.subst σ) p.2
  publicPieces : ∀ p ∈ pieces, p.1.Public restricted
  budget : (pieces.map (fun p => p.1.nodeCount + 1)).sum = source.nodeCount + 1
  value : EqE (source.subst σ) target

private theorem pair_preimage {A B : Type} (f : A → B) (xs : Multiset A) (a b : B)
    (rest : Multiset B) (he : xs.map f = {a, b} + rest) :
    ∃ x y tail, xs = x ::ₘ y ::ₘ tail ∧ f x = a ∧ f y = b ∧ tail.map f = rest := by
  classical
  have he' : xs.map f = a ::ₘ b ::ₘ rest := by simpa using he
  obtain ⟨x, hx, hxa, hrest⟩ := (Multiset.map_eq_cons f xs (b ::ₘ rest) a).mpr he'
  obtain ⟨ys, rfl⟩ := Multiset.exists_cons_of_mem hx
  simp only [Multiset.erase_cons_head] at hrest
  obtain ⟨y, hy, hyb, ht⟩ := (Multiset.map_eq_cons f ys rest b).mpr hrest
  obtain ⟨tail, rfl⟩ := Multiset.exists_cons_of_mem hy
  simp only [Multiset.erase_cons_head] at ht
  exact ⟨x, y, tail, rfl, hxa, hyb, ht⟩

namespace MultiplicationPartition
variable {restricted : Finset Nat} {σ : V → Term W} {r : Term V} {a b : Term W}

/-- The empty-rewrite E0 endpoint case preserves all recipe witnesses. -/
def of_base (p : MultiplicationPartition restricted σ r a) (he : BaseEq a b) :
    MultiplicationPartition restricted σ r b where
  pieces := p.pieces
  sourceFactors := p.sourceFactors
  targetFactors := p.targetFactors.trans he.mul_factors
  values := p.values
  publicPieces := p.publicPieces
  budget := p.budget
  value := p.value.trans he.sound

/-- Every outer fusion merges exactly two recipe occurrences into a product.
The remainder and total node-count budget are retained, even for duplicates. -/
theorem fusion (p : MultiplicationPartition restricted σ r a) (h : OuterFusion a b) :
    Nonempty (MultiplicationPartition restricted σ r b) := by
  obtain ⟨inputs, output, rest, ⟨k, nr, ns, m, n, rfl, rfl⟩, hs, ht⟩ := h
  have hpair : p.pieces.map (fun q => q.2.baseClass) =
      {(.ternary .penc k nr m : Term W).baseClass, (.ternary .penc k ns n : Term W).baseClass} + rest :=
    p.targetFactors.trans hs
  obtain ⟨x, y, tail, hp, hx, hy, htail⟩ := pair_preimage _ _ _ _ _ hpair
  let z : Term V × Term W := (.binary .mul x.1 y.1, combinedCiphertext k nr ns m n)
  have hxm : x ∈ p.pieces := by rw [hp]; simp
  have hym : y ∈ p.pieces := by rw [hp]; simp
  have hz : EqE (z.1.subst σ) z.2 :=
    (EqE.binary .mul ((p.values x hxm).trans ((baseClass_eq_iff _ _).mp hx).sound)
      ((p.values y hym).trans ((baseClass_eq_iff _ _).mp hy).sound)).trans
        (RootStep.homomorphic k nr ns m n).sound
  refine ⟨{
    pieces := z ::ₘ tail
    sourceFactors := ?_
    targetFactors := ?_
    values := ?_
    publicPieces := ?_
    budget := ?_
    value := p.value.trans (OuterFusion.to_modulo ⟨_, _, rest, ⟨k, nr, ns, m, n, rfl, rfl⟩, hs, ht⟩).sound
  }⟩
  · have hh := p.sourceFactors
    rw [hp] at hh
    simpa only [Multiset.map_cons, Multiset.sum_cons, z, Term.mulFactors, add_assoc] using hh
  · simp only [Multiset.map_cons, z, htail]
    simpa using ht.symm
  · intro q hq
    rcases Multiset.mem_cons.mp hq with rfl | hq
    · exact hz
    · exact p.values q (by rw [hp]; simp [hq])
  · intro q hq
    rcases Multiset.mem_cons.mp hq with rfl | hq
    · exact ⟨p.publicPieces x hxm, p.publicPieces y hym⟩
    · exact p.publicPieces q (by rw [hp]; simp [hq])
  · have hh := p.budget
    rw [hp] at hh
    simp only [Multiset.map_cons, Multiset.sum_cons, z, Term.nodeCount] at hh ⊢
    omega

/-- All actual paths from a normal factor family preserve a public recipe
partition, with exact factors and the unchanged original recipe budget. -/
theorem reduces (p : MultiplicationPartition restricted σ r a)
    (ha : a.NormalMulFactors) (h : ReducesModulo a b) :
    Nonempty (MultiplicationPartition restricted σ r b) := by
  revert p ha
  induction h with
  | base he => exact fun p _ => ⟨p.of_base he⟩
  | head hs _ ih =>
    intro p ha
    have hm := hs.normal_mul_factors ha
    obtain ⟨p'⟩ := p.fusion hm.1
    exact ih p' hm.2

/-- If at least two final pieces remain, every piece's recipe is strictly
smaller than the original source. Even a one-node other piece consumes budget. -/
theorem piece_smaller (p : MultiplicationPartition restricted σ r a)
    (hc : 2 ≤ p.pieces.card) (q : Term V × Term W) (hq : q ∈ p.pieces) :
    q.1.nodeCount < r.nodeCount := by
  obtain ⟨rest, hr⟩ := Multiset.exists_cons_of_mem hq
  have hb := p.budget
  rw [hr] at hb hc
  cases rest using Multiset.induction_on with
  | empty => simp at hc
  | cons z tail _ =>
    have := z.1.nodeCount_pos
    simp only [Multiset.map_cons, Multiset.sum_cons] at hb
    omega

/-- A non-ciphertext multiplication normal form has at least two factors, so
its partition exposes only strictly smaller public recipe comparisons. -/
theorem normal_product_pieces_smaller (p : MultiplicationPartition restricted σ r a)
    {x y : Term W} (he : a = .binary .mul x y) (q : Term V × Term W) (hq : q ∈ p.pieces) :
    q.1.Public restricted ∧ q.1.nodeCount < r.nodeCount := by
  subst a
  have hc := congrArg Multiset.card p.targetFactors
  have hx := Multiset.card_pos.mpr x.mulFactors_nonempty
  have hy := Multiset.card_pos.mpr y.mulFactors_nonempty
  simp only [Multiset.card_map, Term.mulFactors, Multiset.card_add] at hc
  exact ⟨p.publicPieces q hq, p.piece_smaller (by omega) q hq⟩

end MultiplicationPartition
end ExplainableCrypto.Helios.Symbolic
