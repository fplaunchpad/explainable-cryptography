import ExplainableCrypto.Helios.Model

namespace ExplainableCrypto.Helios

theorem replay_accepted :
    check .original [publicBoard.alice, publicBoard.bob]
      ((Recipe.replay false).submit publicBoard) = none := by decide

theorem replay_tallies :
    (run .original false (.replay false)).outcome = .tallied (2, 1) ∧
    (run .original true (.replay false)).outcome = .tallied (1, 2) := by decide

/-- One recipe and one public test distinguish the two worlds. -/
theorem replay_distinguishes :
    xCountIs 2 (run .original false (.replay false)) = true ∧
    xCountIs 2 (run .original true (.replay false)) = false := by decide

theorem original_not_private : ¬ RestrictedPrivacy .original := by
  intro h
  have hx := congrArg (xCountIs 2) (h (.replay false))
  have hn : xCountIs 2 (run .original false (.replay false)) ≠
      xCountIs 2 (run .original true (.replay false)) := by decide
  exact hn hx

end ExplainableCrypto.Helios
