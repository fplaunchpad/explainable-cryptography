import ExplainableCrypto.Helios.Model

namespace ExplainableCrypto.Helios

/-- The certificate remains attached to the same unordered product. -/
theorem swap_preserves_validity (b : Ballot) : valid b.swap = valid b := by
  simp only [valid, Ballot.swap, sameAggregate]
  cases h₁ : (b.x.proof == b.x.ciphertext) <;>
    cases h₂ : (b.y.proof == b.y.ciphertext) <;> simp_all [Bool.and_comm, Bool.or_comm]

theorem permuted_ballot_distinct :
    (Recipe.permute false).submit publicBoard ≠ publicBoard.alice ∧
    (Recipe.permute false).submit publicBoard ≠ publicBoard.bob := by decide

theorem permutation_accepted :
    check .wholeBallot [publicBoard.alice, publicBoard.bob]
      ((Recipe.permute false).submit publicBoard) = none := by decide

theorem permutation_tallies :
    (run .wholeBallot false (.permute false)).outcome = .tallied (1, 2) ∧
    (run .wholeBallot true (.permute false)).outcome = .tallied (2, 1) := by decide

theorem permutation_distinguishes :
    xCountIs 1 (run .wholeBallot false (.permute false)) = true ∧
    xCountIs 1 (run .wholeBallot true (.permute false)) = false := by decide

theorem wholeBallot_not_private : ¬ RestrictedPrivacy .wholeBallot := by
  intro h
  have hx := congrArg (xCountIs 1) (h (.permute false))
  have hn : xCountIs 1 (run .wholeBallot false (.permute false)) ≠
      xCountIs 1 (run .wholeBallot true (.permute false)) := by decide
  exact hn hx

end ExplainableCrypto.Helios
