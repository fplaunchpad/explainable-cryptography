import ExplainableCrypto.Helios.Symbolic.HistoricalMinimumOrigins
import ExplainableCrypto.Helios.Symbolic.ProjectionNormalForms

namespace ExplainableCrypto.Helios.Symbolic.Historical
variable {n : Nat}

/-- Every minimum decrypt is covered, without an assumed right-argument value or certificate. -/
theorem minimum_decryption_no_match (ns : Names n) (swap : Bool)
    (left right : Fin (n + 1)) (restricted : Finset Nat) (a b : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value (.binary .dec a b))
    (out : Ground) :
    ¬ DecryptionMatch ((frame ns swap left right).eval a) ((frame ns swap left right).eval b) out := by
  have hb := hm.subterm (.binaryRight .dec a .hole)
  exact hm.no_decryption_match_of_certificates
    (minimum_pair_and_ciphertext_origins ns swap left right restricted b hb).2 out

theorem minimum_decryption_path (ns : Names n) (swap : Bool)
    (left right : Fin (n + 1)) (restricted : Finset Nat) (a b : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value (.binary .dec a b))
    {t : Ground} (ht : ReducesModulo ((frame ns swap left right).eval (.binary .dec a b)) t) :
    ∃ a' b', ReducesModulo ((frame ns swap left right).eval a) a' ∧
      ReducesModulo ((frame ns swap left right).eval b) b' ∧ BaseEq t (.binary .dec a' b') := by
  rcases ht.decryption_cases with hs | ⟨out, hd, _⟩
  · exact hs
  · exact False.elim (minimum_decryption_no_match ns swap left right restricted a b hm out hd)

theorem minimum_decryption_normal_form (ns : Names n) (swap : Bool)
    (left right : Fin (n + 1)) (restricted : Finset Nat) (a b : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value (.binary .dec a b))
    {a' b' t : Ground} (ha : Irreducible a') (hb : Irreducible b') (ht : Irreducible t)
    (hea : EqE ((frame ns swap left right).eval a) a')
    (heb : EqE ((frame ns swap left right).eval b) b')
    (he : EqE ((frame ns swap left right).eval (.binary .dec a b)) t) :
    BaseEq t (.binary .dec a' b') :=
  decryption_normal_form_of_no_match _ _
    (minimum_decryption_no_match ns swap left right restricted a b hm) ha hb ht hea heb he

theorem minimum_decryption_normal_shape (ns : Names n) (swap : Bool)
    (left right : Fin (n + 1)) (restricted : Finset Nat) (a b : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value (.binary .dec a b))
    {t : Ground} (ht : Irreducible t)
    (he : EqE ((frame ns swap left right).eval (.binary .dec a b)) t) :
    ∃ a' b', t = .binary .dec a' b' ∧ EqE ((frame ns swap left right).eval a) a' ∧
      EqE ((frame ns swap left right).eval b) b' :=
  decryption_normal_shape_of_no_match _ _
    (minimum_decryption_no_match ns swap left right restricted a b hm) ht he

/-- A pair-producing argument of a minimum projection must be a valid honest tuple tail. -/
theorem minimum_projection_argument_tail (ns : Names n) (swap : Bool)
    (left right : Fin (n + 1)) (restricted : Finset Nat) (f : Unary)
    (hf : f = .fst ∨ f = .snd) (a : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value (.unary f a))
    {x y : Ground} (he : EqE ((frame ns swap left right).eval a) (.binary .pair x y)) :
    ∃ i : Fin 2, ∃ j, j < fieldCount n ∧ a = (Term.var i.succ).drop j := by
  have ha := hm.subterm (.unary f .hole)
  rcases minimum_pair_origin ns swap left right restricted a ha he with ⟨p, q, rfl⟩ | ⟨v, hc⟩
  · rcases hf with rfl | rfl
    · exact False.elim (hm.raw_irreducible _ (RootStep.fst p q).to_rewrite)
    · exact False.elim (hm.raw_irreducible _ (RootStep.snd p q).to_rewrite)
  · fin_cases v
    · exact False.elim (hc.not_pair_of_handle
        (σ := (frame ns swap left right).value) (fun _ _ => pk_not_eqE_pair _ _ _) x y he)
    · obtain ⟨j, hj, hr⟩ := voter_projection_pair_origin ns swap left right 0 hc he
      exact ⟨0, j, hj, hr⟩
    · obtain ⟨j, hj, hr⟩ := voter_projection_pair_origin ns swap left right 1 hc he
      exact ⟨1, j, hj, hr⟩

/-- The binary-selector version of (*): a valid honest tail argument is the
only exception to composing separately normal argument/result values modulo E0. -/
theorem minimum_projection_normal_form (ns : Names n) (swap : Bool)
    (left right : Fin (n + 1)) (restricted : Finset Nat) (f : Unary)
    (hf : f = .fst ∨ f = .snd) (a : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value (.unary f a))
    {a' t : Ground} (ha : Irreducible a') (ht : Irreducible t)
    (hea : EqE ((frame ns swap left right).eval a) a')
    (he : EqE ((frame ns swap left right).eval (.unary f a)) t) :
    (∃ i : Fin 2, ∃ j, j < fieldCount n ∧ a = (Term.var i.succ).drop j) ∨
      BaseEq t (.unary f a') := by
  classical
  by_cases hp : ∃ x y, EqE ((frame ns swap left right).eval a) (.binary .pair x y)
  · obtain ⟨x, y, hp⟩ := hp
    exact Or.inl (minimum_projection_argument_tail ns swap left right restricted f hf a hm hp)
  · exact Or.inr (projection_normal_form_of_no_pair f hf _
      (fun x y he => hp ⟨x, y, he⟩) ha ht hea he)

end ExplainableCrypto.Helios.Symbolic.Historical
