import ExplainableCrypto.Helios.Symbolic.ExpandedProofOrigins

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

theorem expanded_component_proof_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (i : Fin 2) (j : Fin (n+1)) :
    EqE ((expandedFrame ns swap left right rs).eval ((Term.var (expandedOld i.succ)).project (n+1+j.val)))
      (componentProof ns i (choice swap left right i).value j) := by
  simpa only [Frame.eval,Term.subst_project,Term.subst,expanded_frame_old,frame_voter_handle] using
    ballot_project_proof ns i (choice swap left right i).value j

theorem expanded_aggregate_proof_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (i : Fin 2) :
    EqE ((expandedFrame ns swap left right rs).eval ((Term.var (expandedOld i.succ)).project (2*(n+1))))
      (aggregateProof ns i (choice swap left right i).value) := by
  simpa only [Frame.eval,Term.subst_project,Term.subst,expanded_frame_old,frame_voter_handle] using
    ballot_project_aggregate ns i (choice swap left right i).value

/-- An exact syntactic embedding permits reusing B7 for all borrowed proof
comparisons without transferring minimum sizes across frame presentations. -/
theorem expanded_borrowed_proof_old (restricted : Finset Nat) (r : Recipe (ExpandedHandles n))
    (hr : ExpandedBorrowedProofForm r) :
    ∃ old : Recipe 3, old.Public restricted ∧ r = old.subst (fun i => .var (expandedOld i)) := by
  rcases hr with ⟨i,j,rfl⟩ | ⟨i,rfl⟩
  · exact ⟨(Term.var i.succ).project (n+1+j.val),Term.Public.project (by trivial) _,by simp only [Term.subst_project,Term.subst]⟩
  · exact ⟨(Term.var i.succ).project (2*(n+1)),Term.Public.project (by trivial) _,by simp only [Term.subst_project,Term.subst]⟩

theorem expanded_constructed_proof_not_component (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (a b c d : Recipe (ExpandedHandles n))
    (hb : b.Public ns.restricted) (i : Fin 2) (j : Fin (n+1)) :
    ¬ EqE ((expandedFrame ns swap left right rs).eval (.spk a b c d))
      (componentProof ns i (choice swap left right i).value j) := by
  intro he
  exact (expanded_frame_opaque_protected ns swap left right rs hp).name_not_deducible b hb
    (Finset.mem_union_right _ (ns.nonce_mem_nonceNames i j)) ((EqE.spk_iff _ _ _ _ _ _ _ _).mp he).2.1

theorem expanded_constructed_proof_not_aggregate (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (a b c d : Recipe (ExpandedHandles n))
    (hb : b.Public ns.restricted) (i : Fin 2) :
    ¬ EqE ((expandedFrame ns swap left right rs).eval (.spk a b c d))
      (aggregateProof ns i (choice swap left right i).value) := by
  intro he
  apply (expanded_frame_opaque_protected ns swap left right rs hp).name_factor_not_deducible b hb
    (Finset.mem_union_right _ (ns.nonce_mem_nonceNames i 0)) _ ?_ ((EqE.spk_iff _ _ _ _ _ _ _ _).mp he).2.1
  apply (mem_foldCandidates_compose _ _).mpr
  exact ⟨0,by simp [Term.composeFactors]⟩

theorem expanded_constructed_proof_not_borrowed (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (a b c d r : Recipe (ExpandedHandles n))
    (hb : b.Public ns.restricted) (hr : ExpandedBorrowedProofForm r) :
    ¬ EqE ((expandedFrame ns swap left right rs).eval (.spk a b c d))
      ((expandedFrame ns swap left right rs).eval r) := by
  intro he
  rcases hr with ⟨i,j,rfl⟩ | ⟨i,rfl⟩
  · exact expanded_constructed_proof_not_component ns swap left right rs hp a b c d hb i j
      (he.trans (expanded_component_proof_value ns swap left right rs i j))
  · exact expanded_constructed_proof_not_aggregate ns swap left right rs hp a b c d hb i
      (he.trans (expanded_aggregate_proof_value ns swap left right rs i))

/-- Four minimum public arguments give a minimum proof constructor even when
its arguments use published partial/result handles. -/
theorem expanded_minimum_spk_of_children (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (a b c d : Recipe (ExpandedHandles n))
    (ha : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value a)
    (hb : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value b)
    (hc : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value c)
    (hd : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value d) :
    MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (.spk a b c d) := by
  have hpub : (Term.spk a b c d).Public ns.restricted := ⟨ha.isPublic,hb.isPublic,hc.isPublic,hd.isPublic⟩
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (expandedFrame ns swap left right rs).value) _ hpub
  rcases expanded_minimum_proof_form ns swap left right rs hn ns.restricted m hm he.symm with ⟨u,v,w,x,rfl⟩ | hborrow
  · have hargs := (EqE.spk_iff _ _ _ _ _ _ _ _).mp he
    have hu := ha.least u hm.isPublic.1 hargs.1
    have hv := hb.least v hm.isPublic.2.1 hargs.2.1
    have hw := hc.least w hm.isPublic.2.2.1 hargs.2.2.1
    have hx := hd.least x hm.isPublic.2.2.2 hargs.2.2.2
    exact hm.of_equivalent_size hpub he (by simp only [Term.nodeCount]; omega)
  · exact False.elim (expanded_constructed_proof_not_borrowed ns swap left right rs hp a b c d m hb.isPublic hborrow he)

/-- Honest proof comparisons reuse initial static equivalence. Constructed
comparisons retain all four smaller tests; nonce protection excludes mixed pairs. -/
theorem expanded_proof_form_equality_swap (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (r s : Recipe (ExpandedHandles n))
    (hr : r.Public ns.restricted) (hs : s.Public ns.restricted)
    (hfr : ExpandedProofRecipeForm r) (hfs : ExpandedProofRecipeForm s)
    (hobs : (expandedFrame ns false left right rs).ObservationsBelow (expandedFrame ns true left right rs)
      (r.nodeCount+s.nodeCount)) :
    EqE ((expandedFrame ns false left right rs).eval r) ((expandedFrame ns false left right rs).eval s) ↔
    EqE ((expandedFrame ns true left right rs).eval r) ((expandedFrame ns true left right rs).eval s) := by
  rcases hfr with ⟨a,b,c,d,rfl⟩ | hborrow
  · rcases hfs with ⟨a',b',c',d',rfl⟩ | hborrow'
    · exact constructed_proof_equality_transfer _ _ a b c d a' b' c' d' hr hs hobs
    · exact iff_of_false
        (expanded_constructed_proof_not_borrowed ns false left right rs hp a b c d s hr.2.1 hborrow')
        (expanded_constructed_proof_not_borrowed ns true left right rs hp a b c d s hr.2.1 hborrow')
  · rcases hfs with ⟨a,b,c,d,rfl⟩ | hborrow'
    · exact iff_of_false
        (fun he => expanded_constructed_proof_not_borrowed ns false left right rs hp a b c d r hs.2.1 hborrow he.symm)
        (fun he => expanded_constructed_proof_not_borrowed ns true left right rs hp a b c d r hs.2.1 hborrow he.symm)
    · obtain ⟨u,hu,rfl⟩ := expanded_borrowed_proof_old ns.restricted r hborrow
      obtain ⟨v,hv,rfl⟩ := expanded_borrowed_proof_old ns.restricted s hborrow'
      simpa only [expanded_old_recipe_value] using initial_frame_staticEq ns hf left right u v hu hv

theorem expanded_minimum_proof_equality_swap (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns false left right rs)
    (r s : Recipe (ExpandedHandles n))
    (hr : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value r)
    (hs : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value s) {a b c d a' b' c' d' : Ground}
    (her : EqE ((expandedFrame ns false left right rs).eval r) (.spk a b c d))
    (hes : EqE ((expandedFrame ns false left right rs).eval s) (.spk a' b' c' d'))
    (hobs : (expandedFrame ns false left right rs).ObservationsBelow (expandedFrame ns true left right rs)
      (r.nodeCount+s.nodeCount)) :
    EqE ((expandedFrame ns false left right rs).eval r) ((expandedFrame ns false left right rs).eval s) ↔
    EqE ((expandedFrame ns true left right rs).eval r) ((expandedFrame ns true left right rs).eval s) :=
  expanded_proof_form_equality_swap ns hf left right rs hp r s hr.isPublic hs.isPublic
    (expanded_minimum_proof_form ns false left right rs hn ns.restricted r hr her)
    (expanded_minimum_proof_form ns false left right rs hn ns.restricted s hs hes) hobs

theorem accepted_expanded_minimum_proof_equality_swap (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r s : Recipe (ExpandedHandles n))
    (hr : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value r)
    (hs : MinimalRecipe ns.restricted (expandedFrame ns false left right rs).value s) {a b c d a' b' c' d' : Ground}
    (her : EqE ((expandedFrame ns false left right rs).eval r) (.spk a b c d))
    (hes : EqE ((expandedFrame ns false left right rs).eval s) (.spk a' b' c' d'))
    (hobs : (expandedFrame ns false left right rs).ObservationsBelow (expandedFrame ns true left right rs)
      (r.nodeCount+s.nodeCount)) :
    EqE ((expandedFrame ns false left right rs).eval r) ((expandedFrame ns false left right rs).eval s) ↔
    EqE ((expandedFrame ns true left right rs).eval r) ((expandedFrame ns true left right rs).eval s) :=
  expanded_minimum_proof_equality_swap ns hf left right rs hp
    (accepted_expanded_results_numeric ns hf left right rs hp ha false) r s hr hs her hes hobs

end ExplainableCrypto.Helios.Symbolic.Historical.General
