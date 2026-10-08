import ExplainableCrypto.Helios.Symbolic.HistoricalMinimumOrigins

namespace ExplainableCrypto.Helios.Symbolic.Historical
variable {n : Nat}

/-- Exact historical ciphertext recipe forms. No arbitrary constant-value leaf
or unclassified selector is admitted by this syntax predicate. -/
inductive CiphertextRecipeForm (n : Nat) : Recipe 3 → Prop where
  | constructed (k r m : Recipe 3) : CiphertextRecipeForm n (.ternary .penc k r m)
  | honest (i : Fin 2) (j : Fin (n + 1)) :
      CiphertextRecipeForm n ((Term.var i.succ).project j.val)
  | mul {a b : Recipe 3} (ha : CiphertextRecipeForm n a) (hb : CiphertextRecipeForm n b) :
      CiphertextRecipeForm n (.binary .mul a b)

/-- Full-E product inversion supplies a ciphertext value at every selector leaf. -/
theorem ciphertext_form_of_syntax (ns : Names n) (swap : Bool)
    (left right : Fin (n + 1)) {r : Recipe 3} (hs : CiphertextRecipeSyntax r)
    {key nonce message : Ground}
    (he : EqE ((frame ns swap left right).eval r) (.ternary .penc key nonce message)) :
    CiphertextRecipeForm n r := by
  induction hs generalizing key nonce message with
  | constructed k r m => exact .constructed k r m
  | selected v hc =>
    obtain ⟨i, j, _, rfl, _⟩ := frame_projection_ciphertext_origin ns swap left right v hc he
    exact .honest i j
  | mul _ _ ha hb =>
    obtain ⟨_, _, _, _, he₁, he₂, _, _⟩ := he.mul_penc_inversion
    exact .mul (ha he₁) (hb he₂)

/-- Every minimum ciphertext recipe has exact constructed/honest-selector/product syntax. -/
theorem minimum_ciphertext_form (ns : Names n) (swap : Bool)
    (left right : Fin (n + 1)) (restricted : Finset Nat) (r : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value r)
    {key nonce message : Ground}
    (he : EqE ((frame ns swap left right).eval r) (.ternary .penc key nonce message)) :
    CiphertextRecipeForm n r :=
  ciphertext_form_of_syntax ns swap left right
    (minimum_ciphertext_syntax ns swap left right restricted r hm he) he

end ExplainableCrypto.Helios.Symbolic.Historical
