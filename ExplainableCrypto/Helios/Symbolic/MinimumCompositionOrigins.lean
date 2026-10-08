import ExplainableCrypto.Helios.Symbolic.CompositionOriginTools

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

private theorem compose_origin_with_paths (ns : Names n) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value r)
    (hd : ∀ a b, r = .binary .dec a b →
      ∀ m, ¬ DecryptionMatch ((frame ns swap' left right).eval a) ((frame ns swap' left right).eval b) m)
    (hp : ∀ f a, r = .unary f a → (f = .fst ∨ f = .snd) →
      ((frame ns swap' left right).eval a).PairValue → ((frame ns swap left right).eval a).PairValue)
    {x y : Ground} (he : EqE ((frame ns swap' left right).eval r) (.binary .compose x y)) :
    ∃ a b, r = .binary .compose a b := by
  apply (frame ns swap' left right).compose_form_of_paths r ?_ ?_ ?_ he
  · intro v x y hv
    fin_cases v
    · exact arithmetic_not_eqE_pk .compose (Or.inr rfl) _ _ _ hv.symm
    · obtain ⟨a,b,hp⟩ := ballot_tail_pair_value ns swap' left right 0 0 (by unfold fieldCount; omega)
      exact arithmetic_not_eqE_passive_binary .compose .pair (Or.inr rfl) (Or.inl rfl) _ _ _ _ (hv.symm.trans hp)
    · obtain ⟨a,b,hp⟩ := ballot_tail_pair_value ns swap' left right 1 0 (by unfold fieldCount; omega)
      exact arithmetic_not_eqE_passive_binary .compose .pair (Or.inr rfl) (Or.inl rfl) _ _ _ _ (hv.symm.trans hp)
  · intro a b hr out hmatch
    exact False.elim (hd a b hr out hmatch)
  · intro f a hr hf hv
    obtain ⟨u,v,hpair⟩ := hp f a hr hf hv
    subst r
    exact (minimum_successful_projection_form ns swap left right restricted f hf a hm hpair).data_value ns swap' left right

/-- A minimum composition-valued recipe has literal compose syntax. The source
value's components may reduce, and the caller's name policy is retained. -/
theorem minimum_compose_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value r)
    {x y : Ground} (he : EqE ((frame ns swap left right).eval r) (.binary .compose x y)) :
    ∃ a b, r = .binary .compose a b := by
  apply compose_origin_with_paths ns swap swap left right restricted r hm ?_ ?_ he
  · intro a b hr
    subst r
    exact minimum_decryption_no_match ns swap left right restricted a b hm
  · exact fun _ _ _ _ h => h

/-- Smaller public observations prevent a source minimum with another raw head
from acquiring a composition value. No destination minimum size is assumed. -/
theorem minimum_compose_form_after_swap (ns : Names n)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right) r.nodeCount)
    {x y : Ground} (he : EqE ((frame ns true left right).eval r) (.binary .compose x y)) :
    ∃ a b, r = .binary .compose a b := by
  apply compose_origin_with_paths ns false true left right ns.restricted r hm ?_ ?_ he
  · intro a b hr
    subst r
    exact minimum_decryption_failure_swap ns left right a b hm hobs
  · intro f a hr _ hp
    subst r
    exact (minimum_value_shape_reflection ns left right a (hm.subterm (.unary f .hole))
      (hobs.mono (by simp only [Term.nodeCount]; omega))).1 hp

end ExplainableCrypto.Helios.Symbolic.Historical.General
