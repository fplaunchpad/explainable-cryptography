import ExplainableCrypto.Helios.Symbolic.AdditionOriginTools

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

private theorem add_origin_with_paths (ns : Names n) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value r)
    (hd : ∀ a b, r = .binary .dec a b →
      ∀ m, ¬ DecryptionMatch ((frame ns swap' left right).eval a) ((frame ns swap' left right).eval b) m)
    (hp : ∀ f a, r = .unary f a → (f = .fst ∨ f = .snd) →
      ((frame ns swap' left right).eval a).PairValue → ((frame ns swap left right).eval a).PairValue)
    {x y : Ground} (he : EqE ((frame ns swap' left right).eval r) (.binary .add x y)) :
    (∃ a b, r = .binary .add a b) ∨ r = .const .zero ∨ r = .const .one := by
  have h : ((∃ a b, r = .binary .add a b) ∨ r = .const .zero ∨ r = .const .one) ∨ False := by
    apply (frame ns swap' left right).add_form_of_paths r (fun _ => False) ?_ hd ?_ he
    · intro v x y hv
      fin_cases v
      · exact arithmetic_not_eqE_pk .add (Or.inl rfl) _ _ _ hv.symm
      · obtain ⟨a,b,hp⟩ := ballot_tail_pair_value ns swap' left right 0 0 (by unfold fieldCount; omega)
        exact arithmetic_not_eqE_passive_binary .add .pair (Or.inl rfl) (Or.inl rfl) _ _ _ _ (hv.symm.trans hp)
      · obtain ⟨a,b,hp⟩ := ballot_tail_pair_value ns swap' left right 1 0 (by unfold fieldCount; omega)
        exact arithmetic_not_eqE_passive_binary .add .pair (Or.inl rfl) (Or.inl rfl) _ _ _ _ (hv.symm.trans hp)
    · intro f a hr hf hv
      obtain ⟨u,v,hpair⟩ := hp f a hr hf hv
      subst r
      exact (minimum_successful_projection_form ns swap left right restricted f hf a hm hpair).data_value ns swap' left right
  exact h.elim id False.elim

/-- A minimum addition-valued recipe is an addition or one of its two possible
numeric collapses. Reducible supplied summands and arbitrary policies are allowed. -/
theorem minimum_add_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value r)
    {x y : Ground} (he : EqE ((frame ns swap left right).eval r) (.binary .add x y)) :
    (∃ a b, r = .binary .add a b) ∨ r = .const .zero ∨ r = .const .one := by
  apply add_origin_with_paths ns swap swap left right restricted r hm ?_ ?_ he
  · intro a b hr
    subst r
    exact minimum_decryption_no_match ns swap left right restricted a b hm
  · exact fun _ _ _ _ h => h

/-- Smaller observations restrict a destination addition value to raw addition,
zero or one syntax. No destination minimum size is assumed. -/
theorem minimum_add_form_after_swap (ns : Names n)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right) r.nodeCount)
    {x y : Ground} (he : EqE ((frame ns true left right).eval r) (.binary .add x y)) :
    (∃ a b, r = .binary .add a b) ∨ r = .const .zero ∨ r = .const .one := by
  apply add_origin_with_paths ns false true left right ns.restricted r hm ?_ ?_ he
  · intro a b hr
    subst r
    exact minimum_decryption_failure_swap ns left right a b hm hobs
  · intro f a hr _ hp
    subst r
    exact (minimum_value_shape_reflection ns left right a (hm.subterm (.unary f .hole))
      (hobs.mono (by simp only [Term.nodeCount]; omega))).1 hp

end ExplainableCrypto.Helios.Symbolic.Historical.General
