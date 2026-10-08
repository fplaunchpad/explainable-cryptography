import ExplainableCrypto.Helios.Symbolic.ResultHandleSyntax

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Actual numeric results realize a single initial recipe at every derived
handle; this is full-E value equality, not a raw-normalization assertion. -/
theorem result_handle_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (numbers : Fin (n+1) → Nat)
    (hn : ∀ j, EqE (tallyResult ns swap left right rs j) (addNumeral (numbers j)))
    (v : Fin (ResultHandles n)) :
    EqE ((resultFrame ns swap left right rs).value v)
      (((frame ns swap left right).derive (resultNumeralRecipes numbers)).value v) := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) v
  · simp only [resultFrame,Frame.derive,resultEmbedding,resultNumeralRecipes,Fin.addCases_left,
      Frame.eval,Term.subst,expanded_frame_old]
    exact .refl _
  · have hnum (k : Nat) : (addNumeral k).subst (frame ns swap left right).value = addNumeral k := by
      induction k <;> simp_all [addNumeral,Term.subst]
    simpa only [resultFrame,Frame.derive,resultEmbedding,resultNumeralRecipes,Fin.addCases_right,
      Frame.eval,Term.subst,expanded_frame_result,hnum] using hn j

/-- Substitution through every operator gives the same public initial recipe
for arbitrary nested result-only terms. No minimum or size assumption is used. -/
theorem result_recipe_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (numbers : Fin (n+1) → Nat)
    (hn : ∀ j, EqE (tallyResult ns swap left right rs j) (addNumeral (numbers j)))
    (r : Recipe (ResultHandles n)) :
    EqE ((expandedFrame ns swap left right rs).eval (r.subst (fun i => .var (resultEmbedding i))))
      ((frame ns swap left right).eval (r.subst (resultNumeralRecipes numbers))) := by
  have h := r.subst_congr (resultFrame ns swap left right rs).value
    ((frame ns swap left right).derive (resultNumeralRecipes numbers)).value
    (result_handle_value ns swap left right rs numbers hn)
  simpa only [resultFrame,Frame.derive,Frame.eval,Term.subst_subst,Term.subst] using h

/-- One shared numeric table realizes each public result-only recipe in both
assignments. Acceptance supplies the table, including actual zero and large totals. -/
theorem accepted_result_recipe_common_initial (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r : Recipe (ResultHandles n)) (hr : r.Public ns.restricted) :
    ∃ old : Recipe 3, old.Public ns.restricted ∧ ∀ swap : Bool,
      EqE ((expandedFrame ns swap left right rs).eval (r.subst (fun i => .var (resultEmbedding i))))
        ((frame ns swap left right).eval old) := by
  choose numbers _ hn using fun j => accepted_sequence_tally_numeric ns hf left right rs hp haccept j
  exact ⟨r.subst (resultNumeralRecipes numbers),result_recipe_erasure_public numbers r ns.restricted hr,
    fun swap => result_recipe_value ns swap left right rs numbers (fun j => hn j swap) r⟩

/-- Full unbounded static equivalence for the derived old-plus-results frame.
This is a proper subpresentation of the actual frame with trustee partials. -/
theorem accepted_result_frame_staticEq (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs) :
    Frame.StaticEq (resultFrame ns false left right rs) (resultFrame ns true left right rs) := by
  choose numbers _ hn using fun j => accepted_sequence_tally_numeric ns hf left right rs hp haccept j
  have h (swap : Bool) := Frame.staticEq_of_pointwise (result_handle_value ns swap left right rs numbers (fun j => hn j swap))
  exact (h false).trans (((initial_frame_staticEq ns hf left right).derive (resultNumeralRecipes numbers)
    (result_numeral_public numbers ns.restricted)).trans (h true).symm)

/-- Entire tally binding transfers for every public result-only recipe,
including nonminimum wrappers and arbitrarily nested result-handle uses. -/
theorem accepted_result_recipe_tally_binding_swap (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r : Recipe (ResultHandles n)) (hr : r.Public ns.restricted) (j : Fin (n+1)) :
    EqE ((expandedFrame ns swap left right rs).eval (r.subst (fun i => .var (resultEmbedding i))))
      (tallyCiphertext ns swap left right rs j) ↔
    EqE ((expandedFrame ns swap' left right rs).eval (r.subst (fun i => .var (resultEmbedding i))))
      (tallyCiphertext ns swap' left right rs j) := by
  obtain ⟨old,hpublic,hvalue⟩ := accepted_result_recipe_common_initial ns hf left right rs hp haccept r hr
  have h := expanded_old_tally_binding_swap ns hf swap swap' left right rs hp old hpublic j
  simp only [expanded_old_recipe_value] at h
  exact ⟨fun he => (hvalue swap').trans (h.mp ((hvalue swap).symm.trans he)),
    fun he => (hvalue swap).trans (h.mpr ((hvalue swap').symm.trans he))⟩

/-- A matching result-only ciphertext shares its actual result-slot minimum
with either assignment, without any smaller-observation or minimum premises. -/
theorem accepted_result_recipe_bound_tally_shared (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (r : Recipe (ResultHandles n)) (hr : r.Public ns.restricted) (j : Fin (n+1))
    (he : EqE ((expandedFrame ns swap left right rs).eval (r.subst (fun i => .var (resultEmbedding i))))
      (tallyCiphertext ns swap left right rs j)) :
    Frame.SharedMinimum (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs)
      (.binary .dec (.var (expandedPartial j)) (r.subst (fun i => .var (resultEmbedding i)))) :=
  expanded_bound_tally_shared ns swap swap' left right rs j _ he
    ((accepted_result_recipe_tally_binding_swap ns hf swap swap' left right rs hp haccept r hr j).mp he)

/-- Handle renaming neither introduces nor hides restricted literal names. -/
theorem result_recipe_public_iff (r : Recipe (ResultHandles n)) (restricted : Finset Nat) :
    (r.subst (fun i => .var (resultEmbedding i))).Public restricted ↔ r.Public restricted := by
  induction r <;> simp_all only [Term.subst,Term.Public]

/-- Every remaining binding case must lack a result-only recipe presentation.
This assembles the reduction at the exact original induction bound. -/
theorem accepted_expanded_trustee_binding_of_remaining_recipes (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (hremaining : ∀ (j : Fin (n+1)) (b : Recipe (ExpandedHandles n)),
      MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value b →
      (¬ ∃ r : Recipe (ResultHandles n), b = r.subst (fun i => .var (resultEmbedding i))) →
      EqE ((expandedFrame ns swap left right rs).eval b) (tallyCiphertext ns swap left right rs j) →
      Frame.SharedMinimaBelow (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs)
        (Term.binary .dec (.var (expandedPartial j)) b).nodeCount →
      Frame.SharedMinimaBelow (expandedFrame ns swap' left right rs) (expandedFrame ns swap left right rs)
        (Term.binary .dec (.var (expandedPartial j)) b).nodeCount →
      EqE ((expandedFrame ns swap' left right rs).eval b) (tallyCiphertext ns swap' left right rs j)) :
    ExpandedTrusteeBindingTransport ns swap swap' left right rs := by
  classical
  intro j b hm he hforward hreverse
  by_cases horigin : ∃ r : Recipe (ResultHandles n), b = r.subst (fun i => .var (resultEmbedding i))
  · obtain ⟨r,rfl⟩ := horigin
    exact (accepted_result_recipe_tally_binding_swap ns hf swap swap' left right rs hp haccept r
      ((result_recipe_public_iff r ns.restricted).mp hm.isPublic) j).mp he
  · exact hremaining j b hm horigin he hforward hreverse

end ExplainableCrypto.Helios.Symbolic.Historical.General
