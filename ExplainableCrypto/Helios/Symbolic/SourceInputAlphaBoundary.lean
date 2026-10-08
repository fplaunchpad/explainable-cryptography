import ExplainableCrypto.Helios.Symbolic.SourceChannelPreservation

namespace ExplainableCrypto.Helios.Symbolic.SourceInputAlphaBoundary
open Historical General Source

abbrev keyAndInput (secret : Nat) : Extended (Fin 1) :=
  .par (.active 0 (.unary .pk (.name secret))) (.plain (.input 0 (.output 0 (.var none) .nil)))

theorem keyAndInput_wellFormed (secret : Nat) : (keyAndInput secret).WellFormed := by
  constructor
  · simp [Extended.UniqueDefinitions,Extended.Exports]
  · apply Extended.closed_of_all_exports
    intro v
    fin_cases v
    exact Or.inl rfl

/-- Alpha changes both the private binder and its retained key occurrence. -/
theorem private_key_alpha_representative :
    Named.Structural (.newName (.base 40) (.embed (keyAndInput 40)))
      (.newName (.base 41) (.embed (keyAndInput 41))) := by
  simpa [keyAndInput,Named.mapNames,Extended.mapNames,Agent.mapNames,Term.mapNames] using
    Named.Structural.alphaBase (.embed (keyAndInput 40)) 40 41 (by decide)

/-- The old literal is a fresh free input name after bound-name alpha conversion.
It is distinct from the retained private key's new bound name. -/
theorem old_literal_input_after_alpha :
    Named.FreeStep (.newName (.base 40) (.embed (keyAndInput 40))) (.input 0 (.name 40))
      (.newName (.base 41) (.embed (.par (.active (0 : Fin 1) (.unary .pk (.name 41)))
        (.plain (.output 0 (.name 40) .nil))))) := by
  apply Named.FreeStep.congr private_key_alpha_representative _ (.refl _)
  exact .scopeName _ (by decide) (.embed (.parRight _ (.input _ _ _)))

/-- The recipe condition for the old canonical policy therefore cannot be
inferred from arbitrary named alpha-closed input derivations. -/
theorem fixed_original_recipe_policy_counterexample :
    ¬ (Term.name 40 : Recipe 1).Public {40} ∧
    (Term.name 40 : Recipe 1).Public {41} ∧
    Named.FreeStep (.newName (.base 40) (.embed (keyAndInput 40))) (.input 0 (.name 40))
      (.newName (.base 41) (.embed (.par (.active (0 : Fin 1) (.unary .pk (.name 41)))
        (.plain (.output 0 (.name 40) .nil))))) :=
  ⟨by simp [Term.Public],by simp [Term.Public],old_literal_input_after_alpha⟩
end ExplainableCrypto.Helios.Symbolic.SourceInputAlphaBoundary
