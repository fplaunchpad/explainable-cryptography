import ExplainableCrypto.Helios.Symbolic.ResultHandleTransport
import ExplainableCrypto.Helios.Symbolic.ResultHandleExperiments
import ExplainableCrypto.Helios.Symbolic.ExpandedPublicDecryptionSPOT

namespace ExplainableCrypto.Helios.Symbolic.ResultNonceSPOT
open Historical General
abbrev names := ProofObservationSPOT.oneNames
abbrev left := ProofObservationSPOT.oneLeft
abbrev right := ProofObservationSPOT.oneRight
abbrev oldWorld (swap : Bool) := frame names swap left right
abbrev two : Recipe 3 := .binary .add (.const .one) (.const .one)
abbrev ballot : Recipe 3 := constructorBallot (.var 0) (fun _ : Fin 1 => two) (fun _ => .const .one)
  (fun _ : Fin 2 => .spk (.var 0) two (.const .one) (.ternary .penc (.var 0) two (.const .one)))
abbrev submissions : List (Recipe 3) := [ballot]
abbrev world (swap : Bool) := expandedFrame names swap left right submissions
abbrev honest : Combination (HonestIndex 0) := .mul (.leaf (0,0)) (.leaf (1,0))
abbrev recipe : Recipe (ResultHandles 0) := .binary .mul
  (.ternary .penc (.var (resultOld 0)) (.var (resultSlot 0)) (.const .one))
  ((combinationRecipe honest).subst (fun i => .var (resultOld i)))
abbrev expanded := recipe.subst (fun i => .var (resultEmbedding i))
private theorem submissions_public : ∀ r ∈ submissions, r.Public names.restricted := by
  intro r hr
  simp only [submissions,List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r
  apply constructorBallot_public
  · trivial
  · intro _; exact ⟨trivial,trivial⟩
  · intro _; trivial
  · intro _; exact ⟨trivial,⟨trivial,trivial⟩,trivial,trivial,⟨trivial,trivial⟩,trivial⟩
private theorem by_raw (t u : Ground) (h : normalizeRaw t=u) : EqE t u :=
  h ▸ (normalizeRaw_reachable t).to_modulo.sound
private theorem accepted : (oldWorld false).AcceptsSequence 0 (.var 0) honestBoardRecipes submissions := by
  refine ⟨⟨⟨?_,?_⟩,?_,?_⟩,trivial⟩
  · apply by_raw; decide
  · intro j; fin_cases j; apply by_raw; decide
  · apply by_raw; decide
  · intro earlier hm i j he
    fin_cases i; fin_cases j
    simp only [honestBoardRecipes,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    all_goals
      have h := (normalizeRaw_reachable _).to_modulo.sound.symm.trans
        (he.trans (normalizeRaw_reachable _).to_modulo.sound)
      have hn := ((EqE.penc_iff _ _ _ _ _ _).mp h).2.1
      exact arithmetic_not_eqE_name .add (Or.inl rfl) _ _ _ hn.symm
private theorem result_two (swap : Bool) : EqE (tallyResult names swap left right submissions 0) (addNumeral 2) := by
  have h : EqE (tallyResult names false left right submissions 0) (addNumeral 2) :=
    (normalizeRaw_reachable _).to_modulo.sound.trans (baseEq_of_addSyntaxSummary_eq (by decide)).sound
  cases swap with
  | false => exact h
  | true => exact (accepted_sequence_tally_swap names NumericReflectionSPOT.fixture_names_fresh left right submissions
      submissions_public accepted 0).symm.trans h
private theorem result_literal (swap : Bool) : EqE ((world swap).eval (.var (expandedResult 0)))
    (.binary .add (.const .one) (.const .one)) := by
  rw [Frame.eval,Term.subst,expanded_frame_result]
  exact (result_two swap).trans (.binary .add (EqE.equation .zero_one) (.refl _))
private theorem numeric (swap : Bool) : ExpandedResultsNumeric names swap left right submissions :=
  accepted_expanded_results_numeric names NumericReflectionSPOT.fixture_names_fresh left right submissions submissions_public accepted swap
private theorem shape : expanded = mixedCombinationRecipeWith expandedOld (.var (expandedResult 0)) (.const .one) honest := by
  simp only [Term.subst,Term.subst_subst,result_embedding_old,result_embedding_slot,mixedCombinationRecipeWith,combinationRecipeWith]
private theorem binding (swap : Bool) : EqE ((world swap).eval expanded) (tallyCiphertext names swap left right submissions 0) := by
  have he : EqE ((world swap).eval expanded)
      ((world swap).eval (mixedCombinationRecipeWith expandedOld
        (.binary .add (.const .one) (.const .one)) (.const .one) honest)) := by
    rw [shape]
    exact .binary .mul (.ternary .penc (.refl _) (result_literal swap) (.refl _)) (.refl _)
  apply he.trans
  have ht : EqE ((world swap).eval ((tallyRecipe (n := 0) submissions 0).subst (fun i => .var (expandedOld i))))
      (tallyCiphertext names swap left right submissions 0) := by rw [expanded_old_recipe_value]; exact .refl _
  apply EqE.trans ?_ ht
  exact (EqE.equation (.comm .mul trivial _ _)).trans
    (.binary .mul (.refl _) (by
      have h := (normalizeRaw_reachable ((oldWorld swap).eval (ballot.project 0))).to_modulo.sound
      cases swap <;> exact h.symm))

/-- A public ballot whose nonce is the numeral two is accepted; its extra one
vote yields an actual result of two in both assignments. -/
theorem accepted_numeric_nonce_tally :
    (oldWorld false).AcceptsSequence 0 (.var 0) honestBoardRecipes submissions ∧
    ∀ swap : Bool, EqE (tallyResult names swap left right submissions 0) (addNumeral 2) := ⟨accepted,result_two⟩

/-- The published result can itself supply the adversarial nonce. This gives
a globally minimum ten-node mixed tally binding and a shared result-slot decrypt. -/
theorem minimum_result_nonce_tally_binding (swap swap' : Bool) :
    MinimalRecipe names.restricted (world swap).value expanded ∧ expanded.nodeCount=10 ∧
    EqE ((world swap).eval expanded) (tallyCiphertext names swap left right submissions 0) ∧
    Frame.SharedMinimum (world swap) (world swap') (.binary .dec (.var (expandedPartial 0)) expanded) := by
  have hm : MinimalRecipe names.restricted (world swap).value expanded := by
    rw [shape]
    exact expanded_minimum_mixed_of_minimum_nonce_atomic_payload names NumericReflectionSPOT.fixture_names_fresh swap left right
      submissions submissions_public (numeric swap) (.var (expandedResult 0)) (.const .one) (.of_nodeCount_one trivial rfl) trivial rfl honest
  exact ⟨hm,rfl,binding swap,
    accepted_result_recipe_bound_tally_shared names NumericReflectionSPOT.fixture_names_fresh swap swap' left right submissions
      submissions_public accepted recipe (by trivial) 0 (binding swap)⟩

private def mentionsResult : Recipe (ExpandedHandles 0) → Bool
  | .var v => decide (v=expandedResult 0)
  | .name _ | .const _ => false
  | .unary _ a => mentionsResult a
  | .binary _ a b => mentionsResult a || mentionsResult b
  | .ternary _ a b c => mentionsResult a || mentionsResult b || mentionsResult c
  | .spk a b c d => mentionsResult a || mentionsResult b || mentionsResult c || mentionsResult d
private theorem old_no_result (r : Recipe 3) : mentionsResult (r.subst (fun i => .var (expandedOld i)))=false := by
  induction r with
  | var v => fin_cases v <;> decide
  | _ => simp_all only [Term.subst,mentionsResult,Bool.false_or]

/-- A minimum full-tally match need not have old-only syntax. Erasing its
numeric result is value preserving but increases the raw recipe size to fourteen. -/
theorem old_only_minimum_origin_refuted :
    (¬ ∃ old : Recipe 3, expanded=old.subst (fun i => .var (expandedOld i))) ∧
    recipe.nodeCount=10 ∧ (recipe.subst (resultNumeralRecipes (fun _ : Fin 1 => 2))).nodeCount=14 := by
  refine ⟨?_,rfl,rfl⟩
  rintro ⟨old,he⟩
  have h := old_no_result old
  rw [← he] at h
  exact absurd h (by decide)

end ExplainableCrypto.Helios.Symbolic.ResultNonceSPOT
