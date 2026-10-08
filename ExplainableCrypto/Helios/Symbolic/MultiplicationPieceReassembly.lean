import ExplainableCrypto.Helios.Symbolic.MultiplicationMinimumClosure

namespace ExplainableCrypto.Helios.Symbolic
variable {V W U : Type} {restricted : Finset Nat} {σ : V → Term W} {τ : V → Term U}

/-- Actual term partitions cannot be empty; multiplication has no term unit. -/
theorem MultiplicationPartition.pieces_ne_zero {r : Term V} {t : Term W}
    (p : MultiplicationPartition restricted σ r t) : p.pieces ≠ 0 := by
  intro he
  have hc := Multiset.card_pos.mpr t.mulFactors_nonempty
  rw [← p.targetFactors,he] at hc
  simp at hc

/-- A representative of an actual outer E0 factor has exactly that singleton
factor bag. This excludes hidden products as purported target atoms. -/
theorem Term.mul_factor_singleton_of_mem {a b : Term V} (ha : a.baseClass ∈ b.mulFactors) :
    a.mulFactors = {a.baseClass} := by
  have single (b : Term V) (hb : b.mulFactors = {b.baseClass})
      (h : a.baseClass ∈ b.mulFactors) : a.mulFactors = {a.baseClass} := by
    rw [hb] at h
    have he := Multiset.mem_singleton.mp h
    exact ((baseClass_eq_iff _ _).mp he).mul_factors.trans
      (hb.trans (congrArg (fun q => ({q} : Multiset (BaseClass V))) he.symm))
  induction b with
  | binary f b c ib ic =>
    cases f with
    | mul => exact (Multiset.mem_add.mp ha).elim ib ic
    | _ => exact single _ rfl ha
  | _ => exact single _ rfl ha

/-- Reassemble a nonempty multiset of old pieces and shared minimum witnesses.
Both products have the same target factors; destination equality is preserved
by congruence, and each new partition piece is source-minimum. -/
theorem reassemble_minimum_pieces (xs : Multiset (Term V × Term W)) (hne : xs ≠ 0)
    (hp : ∀ x ∈ xs, x.1.Public restricted)
    (hv : ∀ x ∈ xs, EqE (x.1.subst σ) x.2)
    (hf : ∀ x ∈ xs, x.2.mulFactors = {x.2.baseClass})
    (hm : ∀ x ∈ xs, ∃ m, MinimalRecipe restricted σ m ∧
      EqE (x.1.subst σ) (m.subst σ) ∧ EqE (x.1.subst τ) (m.subst τ)) :
    ∃ r s t, ∃ p : MultiplicationPartition restricted σ r t,
      ∃ q : MultiplicationPartition restricted σ s t,
        p.pieces = xs ∧ r.Public restricted ∧ s.Public restricted ∧
        (∀ x ∈ q.pieces, MinimalRecipe restricted σ x.1) ∧ EqE (r.subst τ) (s.subst τ) := by
  induction xs using Multiset.induction_on with
  | empty => exact False.elim (hne rfl)
  | cons x xs ih =>
    obtain ⟨m,hmin,heσ,heτ⟩ := hm x (by simp)
    let p := MultiplicationPartition.single x.1 x.2 (hp x (by simp)) (hv x (by simp)) (hf x (by simp))
    let q := MultiplicationPartition.single m x.2 hmin.isPublic (heσ.symm.trans (hv x (by simp))) (hf x (by simp))
    have hq : ∀ z ∈ q.pieces, MinimalRecipe restricted σ z.1 := by
      intro z hz
      have he := Multiset.mem_singleton.mp hz
      subst z
      exact hmin
    by_cases hz : xs = 0
    · subst xs
      exact ⟨x.1,m,x.2,p,q,by simp [p,MultiplicationPartition.single],hp x (by simp),hmin.isPublic,hq,heτ⟩
    · obtain ⟨r,s,t,p',q',hpieces,hpr,hps,hmins,hdest⟩ := ih hz
        (fun z hz => hp z (by simp [hz])) (fun z hz => hv z (by simp [hz]))
        (fun z hz => hf z (by simp [hz])) (fun z hz => hm z (by simp [hz]))
      refine ⟨.binary .mul x.1 r,.binary .mul m s,.binary .mul x.2 t,p.mul p',q.mul q',?_,
        ⟨hp x (by simp),hpr⟩,⟨hmin.isPublic,hps⟩,?_,.binary .mul heτ hdest⟩
      · simp only [MultiplicationPartition.mul,p,MultiplicationPartition.single,hpieces,Multiset.singleton_add]
      · intro z hz
        exact (Multiset.mem_add.mp hz).elim (hq z) (hmins z)

end ExplainableCrypto.Helios.Symbolic
