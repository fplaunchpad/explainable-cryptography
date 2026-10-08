import ExplainableCrypto.Helios.Computational.CollisionProbability

/-! Honest proof and encryption coins, all sampled from nonzero scalars as in
the historical construction. Sampling never retries to suppress board collisions. -/

namespace ExplainableCrypto.Helios.Computational

open OracleComp
variable {F : Type} [Field F] [Fintype F]

noncomputable def drawTriple (F : Type) [Field F] [Fintype F] : ProbComp (Fin 3 → F) := do
  let a ← sampleNonzero F
  let b ← sampleNonzero F
  let c ← sampleNonzero F
  pure ![a, b, c]

noncomputable def drawHonestCoins (F : Type) [Field F] [Fintype F] : ProbComp (HonestCoins F) := do
  let witness ← drawTriple F
  let challenge ← drawTriple F
  let response ← drawTriple F
  let nonce ← drawNoncePair F
  pure ⟨![nonce.1, nonce.2], witness, challenge, response⟩

theorem drawNoncePair_nonzero {rs : F × F} (h : rs ∈ support (drawNoncePair F)) :
    rs.1 ≠ 0 ∧ rs.2 ≠ 0 := by
  simp only [drawNoncePair, support_bind, support_pure, Set.mem_iUnion,
    Set.mem_singleton_iff] at h
  obtain ⟨r, hr, s, hs, rfl⟩ := h
  exact ⟨sampleNonzero_ne_zero hr, sampleNonzero_ne_zero hs⟩

theorem drawHonestCoins_nonzero {coins : HonestCoins F}
    (h : coins ∈ support (drawHonestCoins F)) : ∀ i, coins.nonce i ≠ 0 := by
  simp only [drawHonestCoins, support_bind, support_pure, Set.mem_iUnion,
    Set.mem_singleton_iff] at h
  obtain ⟨w, _, e, _, z, _, rs, hrs, rfl⟩ := h
  intro i
  fin_cases i
  · exact (drawNoncePair_nonzero hrs).1
  · exact (drawNoncePair_nonzero hrs).2

theorem drawHonestCoins_noFailure : Pr[⊥ | drawHonestCoins F] = 0 := by
  simp [drawHonestCoins, drawTriple, drawNoncePair, sampleNonzero]

omit [Fintype F] in
theorem not_collisionFree_iff (left right : HonestCoins F) :
    ¬ CollisionFree left right ↔
      BlockedNonce (left.nonce 0) (left.nonce 1) (right.nonce 0) ∨
      BlockedNonce (left.nonce 0) (left.nonce 1) (right.nonce 1) := by
  simp only [CollisionFree, Fin.forall_fin_two, BlockedNonce]
  grind

theorem drawHonestCoins_collision_le (left : HonestCoins F) :
    Pr[fun right => ¬ CollisionFree left right | drawHonestCoins F] ≤
      6 * noncePointBound F := by
  unfold drawHonestCoins
  apply probEvent_bind_le_of_forall_le
  intro witness _
  apply probEvent_bind_le_of_forall_le
  intro challenge _
  apply probEvent_bind_le_of_forall_le
  intro response _
  apply (probEvent_bind_pure_comp (drawNoncePair F)
    (fun nonce => (⟨![nonce.1, nonce.2], witness, challenge, response⟩ : HonestCoins F))
    (fun right => ¬ CollisionFree left right)).trans_le
  simpa only [Function.comp_def, not_collisionFree_iff,
    Matrix.cons_val_zero, Matrix.cons_val_one] using
    pairCollision_probability_le (left.nonce 0) (left.nonce 1)

noncomputable def drawHonestPair (F : Type) [Field F] [Fintype F] :
    ProbComp (HonestCoins F × HonestCoins F) := do
  let left ← drawHonestCoins F
  let right ← drawHonestCoins F
  pure (left, right)

theorem drawHonestPair_collision_le :
    Pr[fun pair => ¬ CollisionFree pair.1 pair.2 | drawHonestPair F] ≤
      6 * noncePointBound F := by
  unfold drawHonestPair
  apply probEvent_bind_le_of_forall_le
  intro left _
  exact (probEvent_bind_pure_comp (drawHonestCoins F) (fun right => (left, right))
    (fun pair => ¬ CollisionFree pair.1 pair.2)).trans_le (drawHonestCoins_collision_le left)

theorem drawHonestPair_support {pair : HonestCoins F × HonestCoins F}
    (h : pair ∈ support (drawHonestPair F)) :
    pair.1 ∈ support (drawHonestCoins F) ∧ pair.2 ∈ support (drawHonestCoins F) := by
  simp only [drawHonestPair, support_bind, support_pure, Set.mem_iUnion,
    Set.mem_singleton_iff] at h
  obtain ⟨alice, ha, bob, hb, rfl⟩ := h
  exact ⟨ha, hb⟩

#print axioms drawHonestCoins_nonzero
#print axioms drawHonestCoins_noFailure
#print axioms drawHonestPair_collision_le

end ExplainableCrypto.Helios.Computational
