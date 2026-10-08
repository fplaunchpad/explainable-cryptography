import ExplainableCrypto.Helios.Symbolic.ExpandedSuccessfulProjections

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

private theorem handle_not_normal_check (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (v : Fin (ExpandedHandles n))
    {k c p : Ground} (ht : Irreducible (.ternary .checkspk k c p)) :
    ¬ EqE ((expandedFrame ns swap left right rs).value v) (.ternary .checkspk k c p) := by
  refine Fin.addCases (fun old => ?_) (fun extra => ?_) v
  · intro he
    have hv : EqE ((frame ns swap left right).value old) (.ternary .checkspk k c p) := by
      simpa only [expandedFrame,Fin.addCases_left] using he
    fin_cases old
    · exact proof_check_not_eqE_pk _ _ _ _ hv.symm
    · obtain ⟨a,b,hp⟩ := ballot_tail_pair_value ns swap left right 0 0 (by unfold fieldCount; omega)
      exact proof_check_not_eqE_passive_binary .pair (Or.inl rfl) _ _ _ _ _ (hv.symm.trans hp)
    · obtain ⟨a,b,hp⟩ := ballot_tail_pair_value ns swap left right 1 0 (by unfold fieldCount; omega)
      exact proof_check_not_eqE_passive_binary .pair (Or.inl rfl) _ _ _ _ _ (hv.symm.trans hp)
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) extra
    · intro he
      have hv : EqE (tallyPartial ns swap left right rs j) (.ternary .checkspk k c p) := by
        simpa only [expandedFrame,Fin.addCases_right,Fin.addCases_left] using he
      exact proof_check_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ _ _ hv.symm
    · intro he
      obtain ⟨number,hnum⟩ := hn j
      have hv : EqE (addNumeral number) (.ternary .checkspk k c p) := hnum.symm.trans
        (by simpa only [expandedFrame,Fin.addCases_right] using he)
      have hh := ((irreducible_eqE_iff_base (addNumeral_irreducible number) ht).mp hv).head_eq
      cases number <;> cases hh

/-- A minimum recipe for any stuck-check value is an explicit check. Target
components may reduce; no target normality or destination premise is assumed. -/
theorem expanded_minimum_stuck_check_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe restricted (expandedFrame ns swap left right rs).value r)
    {k c p : Ground} (hfail : ¬ ProofCheckMatch k c p)
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (.ternary .checkspk k c p)) :
    ∃ a b d, r = .ternary .checkspk a b d := by
  obtain ⟨t,hpath,ht⟩ := exists_normal_form (.ternary .checkspk k c p)
  have he' := hpath.to_modulo.sound
  obtain ⟨a,b,d,rfl,_⟩ := proof_check_normal_shape_of_no_match k c p hfail ht he'
  exact (expandedFrame ns swap left right rs).minimum_normal_check_form_of_origins restricted
    (fun f hf a hm _ _ hp =>
      (expanded_minimum_successful_projection_form ns swap left right rs hn restricted f hf a hm hp).data_value ns swap left right rs)
    (fun a b hm out => expanded_minimum_decryption_no_match ns swap left right rs hn restricted a b hm out)
    r hm ht (fun v => handle_not_normal_check ns swap left right rs hn v ht) (he.trans he')

theorem accepted_expanded_minimum_stuck_check_form (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs) (swap : Bool)
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    {k c p : Ground} (hfail : ¬ ProofCheckMatch k c p)
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (.ternary .checkspk k c p)) :
    ∃ a b d, r = .ternary .checkspk a b d :=
  expanded_minimum_stuck_check_form ns swap left right rs
    (accepted_expanded_results_numeric ns hf left right rs hp ha swap) ns.restricted r hm hfail he

/-- A stuck check of minimum children is minimum; exact origins and ordered
full-E argument injectivity rule out every smaller competing recipe. -/
theorem expanded_minimum_stuck_check_of_children (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (a b c : Recipe (ExpandedHandles n))
    (ha : MinimalRecipe restricted (expandedFrame ns swap left right rs).value a)
    (hb : MinimalRecipe restricted (expandedFrame ns swap left right rs).value b)
    (hc : MinimalRecipe restricted (expandedFrame ns swap left right rs).value c)
    (hfail : ¬ ProofCheckMatch ((expandedFrame ns swap left right rs).eval a)
      ((expandedFrame ns swap left right rs).eval b) ((expandedFrame ns swap left right rs).eval c)) :
    MinimalRecipe restricted (expandedFrame ns swap left right rs).value (.ternary .checkspk a b c) := by
  have hp : (Term.ternary .checkspk a b c).Public restricted := ⟨ha.isPublic,hb.isPublic,hc.isPublic⟩
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (expandedFrame ns swap left right rs).value) _ hp
  obtain ⟨u,v,w,rfl⟩ := expanded_minimum_stuck_check_form ns swap left right rs hn restricted m hm hfail he.symm
  have hargs := (EqE.proof_check_iff_of_no_match _ _ _ _ _ _ hfail (hm.no_proof_check_match u v w)).mp he
  have hu := ha.least u hm.isPublic.1 hargs.1
  have hv := hb.least v hm.isPublic.2.1 hargs.2.1
  have hw := hc.least w hm.isPublic.2.2 hargs.2.2
  exact hm.of_equivalent_size hp he (by simp only [Term.nodeCount]; omega)

theorem expanded_minimum_stuck_check_equality_swap (ns : Names n)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns false left right rs) (r s : Recipe (ExpandedHandles n))
    (hr : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value r)
    (hs : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value s)
    {a b c d e f : Ground} (hnr : ¬ ProofCheckMatch a b c) (hns : ¬ ProofCheckMatch d e f)
    (her : EqE ((expandedFrame ns false left right rs).eval r) (.ternary .checkspk a b c))
    (hes : EqE ((expandedFrame ns false left right rs).eval s) (.ternary .checkspk d e f))
    (hobs : (expandedFrame ns false left right rs).ObservationsBelow (expandedFrame ns true left right rs)
      (r.nodeCount+s.nodeCount)) :
    EqE ((expandedFrame ns false left right rs).eval r) ((expandedFrame ns false left right rs).eval s) ↔
      EqE ((expandedFrame ns true left right rs).eval r) ((expandedFrame ns true left right rs).eval s) := by
  obtain ⟨a',b',c',rfl⟩ := expanded_minimum_stuck_check_form ns false left right rs hn ns.restricted r hr hnr her
  obtain ⟨d',e',f',rfl⟩ := expanded_minimum_stuck_check_form ns false left right rs hn ns.restricted s hs hns hes
  exact minimum_proof_check_equality_transfer _ _ a' b' c' d' e' f' hr hs hobs

theorem accepted_expanded_minimum_stuck_check_equality_swap (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r s : Recipe (ExpandedHandles n))
    (hr : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value r)
    (hs : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value s)
    {a b c d e f : Ground} (hnr : ¬ ProofCheckMatch a b c) (hns : ¬ ProofCheckMatch d e f)
    (her : EqE ((expandedFrame ns false left right rs).eval r) (.ternary .checkspk a b c))
    (hes : EqE ((expandedFrame ns false left right rs).eval s) (.ternary .checkspk d e f))
    (hobs : (expandedFrame ns false left right rs).ObservationsBelow (expandedFrame ns true left right rs)
      (r.nodeCount+s.nodeCount)) :
    EqE ((expandedFrame ns false left right rs).eval r) ((expandedFrame ns false left right rs).eval s) ↔
      EqE ((expandedFrame ns true left right rs).eval r) ((expandedFrame ns true left right rs).eval s) :=
  expanded_minimum_stuck_check_equality_swap ns left right rs
    (accepted_expanded_results_numeric ns hf left right rs hp ha false) r s hr hs hnr hns her hes hobs

end ExplainableCrypto.Helios.Symbolic.Historical.General
