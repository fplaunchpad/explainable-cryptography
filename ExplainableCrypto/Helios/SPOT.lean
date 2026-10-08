import ExplainableCrypto.Helios.Replay
import ExplainableCrypto.Helios.Permutation

/-! Hand-derived fixtures and controls; see `docs/research/helios-model.md`. -/
namespace ExplainableCrypto.Helios

theorem issued_valid : ∀ v : Voter, valid (issued v) = true := by decide

theorem ordinary_tallies : ∀ p : Policy, ∀ w : Bool,
    (run p w (.fresh .x)).outcome = .tallied (2, 1) := by decide

theorem ordinary_not_rejected : ∀ p : Policy, ∀ w : Bool, ∀ reason : Rejection,
    (run p w (.fresh .x)).outcome ≠ .rejected reason := by
  intro p w reason
  rw [ordinary_tallies]
  exact Outcome.noConfusion

theorem tally_not_constant :
    (run .components false (.fresh .x)).outcome ≠
      (run .components false (.fresh .y)).outcome := by decide

theorem fresh_abstention_tallied : ∀ w : Bool,
    (run .components w (.fresh .abstain)).outcome = .tallied (1, 1) := by decide

theorem malformed_rejected : ∀ p : Policy, ∀ w : Bool,
    (run p w .malformed).outcome = .rejected .invalidProof := by decide

theorem malformed_not_tallied : ∀ p : Policy, ∀ w : Bool, ∀ t : Tally,
    (run p w .malformed).outcome ≠ .tallied t := by
  intro p w t
  rw [malformed_rejected]
  exact Outcome.noConfusion

theorem wholeBallot_blocks_replay : ∀ w target : Bool,
    (run .wholeBallot w (.replay target)).outcome =
      .rejected .duplicateBallot := by decide

theorem components_block_replay : ∀ w target : Bool,
    (run .components w (.replay target)).outcome =
      .rejected .reusedCiphertext := by decide

theorem components_block_permutation : ∀ w target : Bool,
    (run .components w (.permute target)).outcome =
      .rejected .reusedCiphertext := by decide

theorem component_rejection_not_invalid_proof :
    valid ((Recipe.permute false).submit publicBoard) = true ∧
    (run .components false (.permute false)).outcome ≠
      .rejected .invalidProof := by decide

/-- Independently check the one-hot encoding for every private vote assignment. -/
theorem issued_aggregate_at_most_one :
    ∀ (a b m : Vote) (v : Voter),
      let s : Secrets := fun who => match who with
        | .alice => a | .bob => b | .mallory => m
      plaintext s (issued v).x.ciphertext + plaintext s (issued v).y.ciphertext ≤ 1 :=
  by decide

/-- Exhaustive finite backstop for the fresh-ballot campaign. -/
theorem fresh_ballots_accepted : ∀ p : Policy, ∀ v : Vote,
    check p [publicBoard.alice, publicBoard.bob]
      ((Recipe.fresh v).submit publicBoard) = none := by decide

/-- Exhaustive finite backstop covering every recipe constructor. -/
theorem recipe_swap_validity : ∀ r : Recipe,
    valid (r.submit publicBoard).swap = valid (r.submit publicBoard) := by decide

end ExplainableCrypto.Helios
