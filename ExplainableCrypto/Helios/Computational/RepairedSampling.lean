import ExplainableCrypto.Helios.Computational.RepairedExecution

/-! Honest acceptance under the repaired weeding rule: all three ciphertext
nonces (two components and their sum) are covered on both sides. Independent
sampling is retained, including every collision and rejection execution. -/

namespace ExplainableCrypto.Helios.Computational

open OracleComp
variable {F : Type} [Field F] [Fintype F]

private theorem three_points_le (a b c : F) :
    Pr[fun x => x = a ∨ x = b ∨ x = c | sampleNonzero F] ≤ 3 * noncePointBound F := by
  have h0 := probEvent_or_le (sampleNonzero F) (fun x => x = a) (fun x => x = b ∨ x = c)
  have h1 := probEvent_or_le (sampleNonzero F) (fun x => x = b) (fun x => x = c)
  simp only [probEvent_eq_eq_probOutput] at h0 h1
  calc
    _ ≤ Pr[= a | sampleNonzero F] + (Pr[= b | sampleNonzero F] + Pr[= c | sampleNonzero F]) :=
      h0.trans (add_le_add_right h1 _)
    _ ≤ noncePointBound F + (noncePointBound F + noncePointBound F) :=
      add_le_add (sampleNonzero_point_le _) (add_le_add (sampleNonzero_point_le _) (sampleNonzero_point_le _))
    _ = _ := by simp [show (3 : ENNReal) = 1 + (1 + 1) by norm_num, add_mul]

theorem nonceSum_blocked_le (r0 r1 : F) :
    Pr[fun rs => BlockedNonce r0 r1 (rs.1 + rs.2) | drawNoncePair F] ≤ 3 * noncePointBound F := by
  unfold drawNoncePair
  apply probEvent_bind_le_of_forall_le
  intro x _
  apply (probEvent_bind_pure_comp (sampleNonzero F) (fun y => (x, y))
    (fun rs => BlockedNonce r0 r1 (rs.1 + rs.2))).trans_le
  have he : (fun y : F => BlockedNonce r0 r1 (x + y)) =
      (fun y => y = r0 - x ∨ y = r1 - x ∨ y = (r0 + r1) - x) := by
    funext y
    simp only [BlockedNonce, eq_sub_iff_add_eq, add_comm x y]
  change Pr[fun y => BlockedNonce r0 r1 (x + y) | sampleNonzero F] ≤ _
  rw [he]
  exact three_points_le _ _ _

def ExpandedCollisionFree (aliceCoins bobCoins : HonestCoins F) : Prop :=
  ∀ i j, bobCoins.coveredNonce i ≠ aliceCoins.coveredNonce j

omit [Fintype F] in
theorem not_expandedCollisionFree_iff (aliceCoins bobCoins : HonestCoins F) :
    ¬ ExpandedCollisionFree aliceCoins bobCoins ↔
      (BlockedNonce (aliceCoins.nonce 0) (aliceCoins.nonce 1) (bobCoins.nonce 0) ∨
        BlockedNonce (aliceCoins.nonce 0) (aliceCoins.nonce 1) (bobCoins.nonce 1)) ∨
      BlockedNonce (aliceCoins.nonce 0) (aliceCoins.nonce 1) (bobCoins.nonce 0 + bobCoins.nonce 1) := by
  simp only [ExpandedCollisionFree, Option.forall, Fin.forall_fin_two, HonestCoins.coveredNonce,
    BlockedNonce]
  grind

theorem expandedPairCollision_probability_le (r0 r1 : F) :
    Pr[fun rs => (BlockedNonce r0 r1 rs.1 ∨ BlockedNonce r0 r1 rs.2) ∨
      BlockedNonce r0 r1 (rs.1 + rs.2) | drawNoncePair F] ≤ 9 * noncePointBound F := by
  calc
    _ ≤ Pr[fun rs => BlockedNonce r0 r1 rs.1 ∨ BlockedNonce r0 r1 rs.2 | drawNoncePair F] +
        Pr[fun rs => BlockedNonce r0 r1 (rs.1 + rs.2) | drawNoncePair F] := probEvent_or_le _ _ _
    _ ≤ 6 * noncePointBound F + 3 * noncePointBound F :=
      add_le_add (pairCollision_probability_le _ _) (nonceSum_blocked_le _ _)
    _ = _ := by rw [← add_mul]; norm_num

theorem drawHonestCoins_expanded_collision_le (aliceCoins : HonestCoins F) :
    Pr[fun bobCoins => ¬ ExpandedCollisionFree aliceCoins bobCoins | drawHonestCoins F] ≤
      9 * noncePointBound F := by
  unfold drawHonestCoins
  apply probEvent_bind_le_of_forall_le
  intro witness _
  apply probEvent_bind_le_of_forall_le
  intro challenge _
  apply probEvent_bind_le_of_forall_le
  intro response _
  apply (probEvent_bind_pure_comp (drawNoncePair F)
    (fun nonce => (⟨![nonce.1, nonce.2], witness, challenge, response⟩ : HonestCoins F))
    (fun bobCoins => ¬ ExpandedCollisionFree aliceCoins bobCoins)).trans_le
  simpa only [Function.comp_def, not_expandedCollisionFree_iff,
    Matrix.cons_val_zero, Matrix.cons_val_one] using
    expandedPairCollision_probability_le (aliceCoins.nonce 0) (aliceCoins.nonce 1)

theorem drawHonestPair_expanded_collision_le :
    Pr[fun pair => ¬ ExpandedCollisionFree pair.1 pair.2 | drawHonestPair F] ≤
      9 * noncePointBound F := by
  unfold drawHonestPair
  apply probEvent_bind_le_of_forall_le
  intro aliceCoins _
  exact (probEvent_bind_pure_comp (drawHonestCoins F) (fun bobCoins => (aliceCoins, bobCoins))
    (fun pair => ¬ ExpandedCollisionFree pair.1 pair.2)).trans_le
      (drawHonestCoins_expanded_collision_le aliceCoins)

variable {G : Type} [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

theorem repairedHonestPair_rejection_le (hash : StatementHash F G) (g pk : G)
    (hg : Function.Injective (fun r : F => r • g)) (vote : Bool) :
    Pr[fun pair => (repairedCastHonestPair hash g pk vote pair.1 pair.2).1 ≠
      (.accepted, .accepted) | drawHonestPair F] ≤ 9 * noncePointBound F := by
  apply le_trans ?_ (drawHonestPair_expanded_collision_le (F := F))
  apply probEvent_mono
  intro pair _ hbad hgood
  apply hbad
  rw [repairedCastHonestPair_eq hash g pk hg vote pair.1 pair.2 hgood]

#print axioms nonceSum_blocked_le
#print axioms drawHonestPair_expanded_collision_le
#print axioms repairedHonestPair_rejection_le

end ExplainableCrypto.Helios.Computational
