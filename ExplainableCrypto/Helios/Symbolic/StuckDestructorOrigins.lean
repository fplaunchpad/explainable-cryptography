import ExplainableCrypto.Helios.Symbolic.StuckMinimumTools

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

private abbrev StuckHead := Term.StuckDestructorHead

private theorem minimum_normal_stuck_head (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value r) {t : Ground}
    (ht : Irreducible t) (hk : StuckHead t)
    (he : EqE ((frame ns swap left right).eval r) t) : (r.subst (fun _ => (.const .bottom : Ground))).headTag = t.headTag := by
  apply (frame ns swap left right).minimum_normal_stuck_head_of_origins restricted
    (fun f hf a hm _ _ hp => (minimum_successful_projection_form ns swap left right restricted f hf a hm hp).data_value ns swap left right)
    (fun a b hm => minimum_decryption_no_match ns swap left right restricted a b hm)
    (fun t ht hk v he => ?_) r hm ht hk he
  have notPair {a b : Ground} (hv : EqE ((frame ns swap left right).value v) (.binary .pair a b)) : False := by
    obtain ⟨_, _, rfl, _⟩ := (hv.symm.trans he).passive_binary_irreducible_shape (Or.inl rfl) ht
    simp [Term.StuckDestructorHead,Term.headTag] at hk
  fin_cases v
  · obtain ⟨_, rfl, _⟩ := he.pk_irreducible_shape ht
    simp [Term.StuckDestructorHead,Term.headTag] at hk
  · obtain ⟨a,b,hp⟩ := ballot_tail_pair_value ns swap left right 0 0 (by unfold fieldCount; omega)
    exact notPair hp
  · obtain ⟨a,b,hp⟩ := ballot_tail_pair_value ns swap left right 1 0 (by unfold fieldCount; omega)
    exact notPair hp

/-- A minimum recipe with a stuck projection value has the same selector and
an argument that cannot reach a pair. Target arguments may themselves reduce. -/
theorem minimum_stuck_projection_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value r)
    (f : Unary) (hf : f = .fst ∨ f = .snd) {a : Ground}
    (hn : ∀ x y, ¬ EqE a (.binary .pair x y))
    (he : EqE ((frame ns swap left right).eval r) (.unary f a)) :
    ∃ b, r = .unary f b ∧ ∀ x y, ¬ EqE ((frame ns swap left right).eval b) (.binary .pair x y) := by
  exact (frame ns swap left right).minimum_stuck_projection_form_of_head restricted
    (fun f hf a hm _ _ hp => (minimum_successful_projection_form ns swap left right restricted f hf a hm hp).data_value ns swap left right)
    (fun r hm _ ht hk he => minimum_normal_stuck_head ns swap left right restricted r hm ht hk he)
    r hm f hf hn he

/-- A minimum recipe with a stuck decryption value has exact ordered dec syntax.
No normality premise is imposed on the target or its arguments. -/
theorem minimum_stuck_decryption_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value r) {a b : Ground}
    (hn : ∀ m, ¬ DecryptionMatch a b m)
    (he : EqE ((frame ns swap left right).eval r) (.binary .dec a b)) :
    ∃ u v, r = .binary .dec u v ∧
      ∀ m, ¬ DecryptionMatch ((frame ns swap left right).eval u) ((frame ns swap left right).eval v) m := by
  exact (frame ns swap left right).minimum_stuck_decryption_form_of_head restricted
    (fun a b hm => minimum_decryption_no_match ns swap left right restricted a b hm)
    (fun r hm _ ht hk he => minimum_normal_stuck_head ns swap left right restricted r hm ht hk he)
    r hm hn he

/-- Forward transfer uses only first-world minima and strictly smaller argument
tests. It does not require that the destination projection remain stuck. -/
theorem minimum_stuck_projection_equality_imp (ns : Names n)
    (left right : CandidateSubstitution n Empty) (r s : Recipe 3)
    (hr : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hs : MinimalRecipe ns.restricted (frame ns false left right).value s)
    (f : Unary) (hf : f = .fst ∨ f = .snd) {a : Ground}
    (hn : ∀ x y, ¬ EqE a (.binary .pair x y))
    (her : EqE ((frame ns false left right).eval r) (.unary f a))
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      (r.nodeCount + s.nodeCount))
    (he : EqE ((frame ns false left right).eval r) ((frame ns false left right).eval s)) :
    EqE ((frame ns true left right).eval r) ((frame ns true left right).eval s) := by
  obtain ⟨u, rfl, hu⟩ := minimum_stuck_projection_form ns false left right ns.restricted r hr f hf hn her
  obtain ⟨v, rfl, hv⟩ := minimum_stuck_projection_form ns false left right ns.restricted s hs f hf hn (he.symm.trans her)
  have harg := ((EqE.projection_iff_of_no_pair f f hf hf _ _ hu hv).mp he).2
  exact .unary f ((hobs u v hr.isPublic hs.isPublic (by simp only [Term.nodeCount]; omega)).mp harg)

/-- Forward decryption transfer compares both ordered arguments. Destination
matching need not be ruled out for this forward congruence implication. -/
theorem minimum_stuck_decryption_equality_imp (ns : Names n)
    (left right : CandidateSubstitution n Empty) (r s : Recipe 3)
    (hr : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hs : MinimalRecipe ns.restricted (frame ns false left right).value s)
    {a b : Ground} (hn : ∀ m, ¬ DecryptionMatch a b m)
    (her : EqE ((frame ns false left right).eval r) (.binary .dec a b))
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      (r.nodeCount + s.nodeCount))
    (he : EqE ((frame ns false left right).eval r) ((frame ns false left right).eval s)) :
    EqE ((frame ns true left right).eval r) ((frame ns true left right).eval s) := by
  obtain ⟨u, v, rfl, huv⟩ := minimum_stuck_decryption_form ns false left right ns.restricted r hr hn her
  obtain ⟨w, x, rfl, hwx⟩ := minimum_stuck_decryption_form ns false left right ns.restricted s hs hn (he.symm.trans her)
  have hargs := (EqE.decryption_iff_of_no_match _ _ _ _ huv hwx).mp he
  have hu := hobs u w hr.isPublic.1 hs.isPublic.1 (by simp only [Term.nodeCount]; omega)
  have hv := hobs v x hr.isPublic.2 hs.isPublic.2 (by simp only [Term.nodeCount]; omega)
  exact .binary .dec (hu.mp hargs.1) (hv.mp hargs.2)

end ExplainableCrypto.Helios.Symbolic.Historical.General
