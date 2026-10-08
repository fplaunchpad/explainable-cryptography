import ExplainableCrypto.Helios.Computational.BallotProofProvenance
import Mathlib.Algebra.Field.ZMod

/-! Algebraic output contract required by joint ballot-proof extraction.
The witnesses must be derived by the extractor; these lemmas do not assume
proof validity implies knowledge or establish a joint extraction probability. -/
namespace ExplainableCrypto.Helios.Computational
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

private theorem encryptWith_injective_pair (g pk : G)
    (hg : Function.Injective (fun r : F => r • g)) (r s m t : F)
    (he : encryptWith g pk r m = encryptWith g pk s t) : r = s ∧ m = t := by
  have hr : r = s := hg (congrArg Prod.fst he)
  have hm := congrArg Prod.snd he
  change m • g + r • pk = t • g + s • pk at hm
  rw [hr] at hm
  exact ⟨hr,hg (add_right_cancel hm)⟩

/-- Witnesses for the actual two components and their implicit aggregate have
consistent nonce and scalar-message sums. This holds in every characteristic. -/
theorem Ballot.covered_witnesses_sum (b : Ballot F G 2) (g pk : G)
    (hg : Function.Injective (fun r : F => r • g))
    (w : Option (Fin 2) → BallotWitness F)
    (hw : ∀ i, (b.coveredStatement g pk i).Witnesses (w i)) :
    (w none).2 = (w (some 0)).2 + (w (some 1)).2 ∧
      voteScalar (w none).1 = (voteScalar (w (some 0)).1 : F) + voteScalar (w (some 1)).1 := by
  have h0 := hw (some 0)
  have h1 := hw (some 1)
  have ha := hw none
  change b.ciphertext 0 = encryptWith g pk (w (some 0)).2 (voteScalar (w (some 0)).1) at h0
  change b.ciphertext 1 = encryptWith g pk (w (some 1)).2 (voteScalar (w (some 1)).1) at h1
  change b.aggregate = encryptWith g pk (w none).2 (voteScalar (w none).1) at ha
  apply encryptWith_injective_pair g pk hg
  rw [← ha]
  simp only [Ballot.aggregate,Fin.sum_univ_two,h0,h1,encryptWith_add]

/-- Excluding characteristic two turns the field equation into the intended
integer at-most-one constraint, retaining abstention and either single vote. -/
theorem Ballot.covered_witnesses_atMostOne (b : Ballot F G 2) (g pk : G)
    (hg : Function.Injective (fun r : F => r • g)) (h2 : (2 : F) ≠ 0)
    (w : Option (Fin 2) → BallotWitness F)
    (hw : ∀ i, (b.coveredStatement g pk i).Witnesses (w i)) :
    (w (some 0)).1.toNat + (w (some 1)).1.toNat = (w none).1.toNat ∧
      (w (some 0)).1.toNat + (w (some 1)).1.toNat ≤ 1 := by
  have hs := (b.covered_witnesses_sum g pk hg w hw).2
  cases h0 : (w (some 0)).1 <;> cases h1 : (w (some 1)).1 <;>
    cases ha : (w none).1 <;> simp_all [voteScalar,← one_add_one_eq_two]


/-- The historical prime scalar field discharges the no-wrap condition from
q > 2; it is not an additional cryptographic hardness assumption. -/
theorem Ballot.covered_witnesses_atMostOne_prime {q : Nat} [Fact q.Prime]
    {H : Type} [AddCommGroup H] [Module (ZMod q) H]
    (b : Ballot (ZMod q) H 2) (g pk : H)
    (hg : Function.Injective (fun r : ZMod q => r • g)) (hq : 2 < q)
    (w : Option (Fin 2) → BallotWitness (ZMod q))
    (hw : ∀ i, (b.coveredStatement g pk i).Witnesses (w i)) :
    (w (some 0)).1.toNat + (w (some 1)).1.toNat = (w none).1.toNat ∧
      (w (some 0)).1.toNat + (w (some 1)).1.toNat ≤ 1 := by
  apply b.covered_witnesses_atMostOne g pk hg ?_ w hw
  exact (ZMod.natCast_eq_zero_iff 2 q).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hq)

#print axioms Ballot.covered_witnesses_atMostOne_prime
#print axioms Ballot.covered_witnesses_sum
#print axioms Ballot.covered_witnesses_atMostOne
end ExplainableCrypto.Helios.Computational
