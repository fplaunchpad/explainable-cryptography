import ExplainableCrypto.Helios.Symbolic.CheckMinimumTools

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

private theorem minimum_normal_check_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value r) {k c p : Ground}
    (ht : Irreducible (.ternary .checkspk k c p))
    (he : EqE ((frame ns swap left right).eval r) (.ternary .checkspk k c p)) :
    ∃ a b d, r = .ternary .checkspk a b d := by
  apply (frame ns swap left right).minimum_normal_check_form_of_origins restricted
    (fun f hf a hm _ _ hp =>
      (minimum_successful_projection_form ns swap left right restricted f hf a hm hp).data_value ns swap left right)
    (fun a b hm out => minimum_decryption_no_match ns swap left right restricted a b hm out)
    r hm ht ?_ he
  intro v hv
  fin_cases v
  · exact proof_check_not_eqE_pk _ _ _ _ hv.symm
  · obtain ⟨a,b,hp⟩ := ballot_tail_pair_value ns swap left right 0 0 (by unfold fieldCount; omega)
    exact proof_check_not_eqE_passive_binary .pair (Or.inl rfl) _ _ _ _ _ (hv.symm.trans hp)
  · obtain ⟨a,b,hp⟩ := ballot_tail_pair_value ns swap left right 1 0 (by unfold fieldCount; omega)
    exact proof_check_not_eqE_passive_binary .pair (Or.inl rfl) _ _ _ _ _ (hv.symm.trans hp)

/-- A minimum recipe with a stuck-check value has exact checkspk syntax.
No target normality is assumed: no-match means no reachable E8/E9 match. -/
theorem minimum_stuck_check_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value r) {k c p : Ground}
    (hn : ¬ ProofCheckMatch k c p)
    (he : EqE ((frame ns swap left right).eval r) (.ternary .checkspk k c p)) :
    ∃ a b d, r = .ternary .checkspk a b d := by
  obtain ⟨t, hpath, ht⟩ := exists_normal_form (.ternary .checkspk k c p)
  have he' := hpath.to_modulo.sound
  obtain ⟨a, b, d, rfl, _⟩ := proof_check_normal_shape_of_no_match k c p hn ht he'
  exact minimum_normal_check_form ns swap left right restricted r hm ht (he.trans he')

/-- The complete stuck-check-valued minimum-recipe branch derives both syntactic
forms and preserves failure via smaller ok probes before comparing arguments. -/
theorem minimum_stuck_check_equality_swap (ns : Names n)
    (left right : CandidateSubstitution n Empty) (r s : Recipe 3)
    (hr : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hs : MinimalRecipe ns.restricted (frame ns false left right).value s)
    {a b c d e f : Ground} (hnr : ¬ ProofCheckMatch a b c) (hns : ¬ ProofCheckMatch d e f)
    (her : EqE ((frame ns false left right).eval r) (.ternary .checkspk a b c))
    (hes : EqE ((frame ns false left right).eval s) (.ternary .checkspk d e f))
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      (r.nodeCount + s.nodeCount)) :
    EqE ((frame ns false left right).eval r) ((frame ns false left right).eval s) ↔
      EqE ((frame ns true left right).eval r) ((frame ns true left right).eval s) := by
  obtain ⟨a', b', c', rfl⟩ := minimum_stuck_check_form ns false left right ns.restricted r hr hnr her
  obtain ⟨d', e', f', rfl⟩ := minimum_stuck_check_form ns false left right ns.restricted s hs hns hes
  exact minimum_proof_check_equality_swap ns left right a' b' c' d' e' f' hr hs hobs

end ExplainableCrypto.Helios.Symbolic.Historical.General
