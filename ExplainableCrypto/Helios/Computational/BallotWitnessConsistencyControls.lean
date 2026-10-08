import ExplainableCrypto.Helios.Computational.BallotWitnessConsistency
import ExplainableCrypto.Helios.Computational.RepairControls
import Mathlib.FieldTheory.Finite.GaloisField

/-! Integer vote-count controls. Characteristic-two examples test the abstract
field model's boundary, not historical large prime-order protocol parameters. -/
namespace ExplainableCrypto.Helios.Computational.BallotWitnessConsistencyControls
open RepairControls (Scalar hashes)

/-- Concrete valid one-vote and abstention witnesses use the actual constructor. -/
theorem honest_integer_counts (vote : Bool) :
    let b := strongHonestBallot hashes.ballot 1 3 vote ExecutionControls.aliceCoins
    let w := ExecutionControls.aliceCoins.coveredWitness vote
    (w (some 0)).1.toNat + (w (some 1)).1.toNat = vote.toNat ∧
      ∀ i, (b.coveredStatement 1 3 i).Witnesses (w i) := by
  dsimp only
  constructor
  · simp [HonestCoins.coveredWitness]
  · intro i
    rw [strongHonestBallot_covered_statement]
    rfl

/-- In characteristic two, both component bits one have aggregate bit zero. -/
def wrappedBallot {F : Type} [Field F] (hash : StatementHash F F) : Ballot F F 2 where
  ciphertext := fun _ => encryptWith 1 1 (1 : F) 1
  proof := fun _ => strongProveVote hash 1 1 true 1 1 1 1
  overall := strongProveVote hash 1 1 false (1+1) 1 1 1

def wrappedWitness {F : Type} [Field F] : Option (Fin 2) → BallotWitness F
  | none => (false,1+1)
  | some _ => (true,1)

theorem wrapped_witnesses {F : Type} [Field F] (h2 : (2 : F) = 0)
    (hash : StatementHash F F) :
    ∀ i, ((wrappedBallot hash).coveredStatement 1 1 i).Witnesses (wrappedWitness (F := F) i) := by
  intro i
  cases i with
  | none =>
    change (∑ _ : Fin 2, encryptWith (1 : F) 1 (1 : F) 1) =
      encryptWith (1 : F) 1 (1+1 : F) 0
    rw [Fin.sum_univ_two,encryptWith_add]
    simp only [one_add_one_eq_two,h2]
  | some i => rfl

theorem wrapped_full_proofs_validate {F : Type} [Field F] (h2 : (2 : F) = 0)
    (hash : StatementHash F F) : (wrappedBallot hash).StrongValid hash 1 1 := by
  constructor
  · intro i
    exact strongProveVote_valid hash 1 1 true 1 1 1 1
  · have ha := wrapped_witnesses h2 hash none
    change (wrappedBallot hash).aggregate = encryptWith 1 1 (1+1 : F) 0 at ha
    rw [ha]
    exact strongProveVote_valid hash 1 1 false (1+1) 1 1 1

theorem wrapped_submission_accepts {F : Type} [Field F] [DecidableEq F]
    (h2 : (2 : F) = 0) (hash : StatementHash F F) :
    (repairedSubmit hash 1 1 0 [] (wrappedBallot hash)).1 = .accepted := by
  rw [repairedSubmit_accepted hash 1 1 0 [] _ (wrapped_full_proofs_validate h2 hash)
    (by simp [Ballot.ExpandedFreshFor])]

/-- Cardinality greater than two does not imply that integer vote counts do not wrap. -/
theorem four_element_counterexample :
    let F := GaloisField 2 2
    2 < Nat.card F ∧ Function.Injective (fun r : F => r • (1 : F)) ∧
      ∀ hash : StatementHash F F,
        (wrappedBallot hash).StrongValid hash 1 1 ∧
        (∀ i, ((wrappedBallot hash).coveredStatement 1 1 i).Witnesses (wrappedWitness (F := F) i)) ∧
        ¬ ((wrappedWitness (F := F) (some 0)).1.toNat +
          (wrappedWitness (F := F) (some 1)).1.toNat ≤ 1) := by
  dsimp only
  have h2 : (2 : GaloisField 2 2) = 0 := CharP.cast_eq_zero _ 2
  refine ⟨?_,?_,fun hash => ⟨wrapped_full_proofs_validate h2 hash,wrapped_witnesses h2 hash,?_⟩⟩
  · rw [GaloisField.card 2 2 (by decide)]
    decide
  · intro a b h
    simpa using h
  · decide

#print axioms honest_integer_counts
#print axioms wrapped_witnesses
#print axioms wrapped_full_proofs_validate
#print axioms wrapped_submission_accepts
#print axioms four_element_counterexample
end ExplainableCrypto.Helios.Computational.BallotWitnessConsistencyControls
