import ExplainableCrypto.Helios.Symbolic.PublishedStaticEquivalence
import ExplainableCrypto.Helios.Symbolic.ResultHandleSPOT
import ExplainableCrypto.Helios.Symbolic.TrusteeFreeExperiments

namespace ExplainableCrypto.Helios.Symbolic.TrusteeFreeSPOT
open Historical General
abbrev bad : Term Nat := .binary .partialDecrypt (.name 0) (.name 40)

/-- The secret comparison is semantic: the key need not literally be a name. -/
theorem reducible_key_rejected :
    ¬ (Term.binary .partialDecrypt (.unary .fst (.binary .pair (.name 0) (.const .zero)))
      (.name (V := Nat) 40)).TrusteeFree 0 := by
  intro h
  exact h.2.2 rfl (RootStep.fst _ _).sound

/-- No cryptographic opaque position hides a forbidden partial from the invariant. -/
theorem opaque_positions_rejected :
    ¬ TrusteeFreeValue 0 (.unary .pk bad) ∧
    ¬ TrusteeFreeValue 0 (.ternary .penc (.name 40) bad (.const .zero)) ∧
    ¬ TrusteeFreeValue 0 (.spk (.name 40) (.const .zero) (.const .one) bad) := by
  refine ⟨?_,?_,?_⟩
  · exact fun h => trustee_partial_not_free _ ((TrusteeFreeValue.pk_iff _).mp h)
  · exact fun h => trustee_partial_not_free _ ((TrusteeFreeValue.penc_iff _ _ _).mp h).2.1
  · exact fun h => trustee_partial_not_free _ ((TrusteeFreeValue.spk_iff _ _ _ _).mp h).2.2.2

/-- E7 cannot remove a forbidden partial used as encryption randomness. -/
theorem homomorphic_erasure_rejected :
    ¬ TrusteeFreeValue 0 (.binary .mul
      (.ternary .penc (.name 40) bad (.const .zero))
      (.ternary .penc (.name 40) (.name 41) (.const .one))) := by
  intro h
  exact trustee_partial_not_free _ ((TrusteeFreeValue.penc_iff _ _ _).mp
    ((TrusteeFreeValue.mul_iff _ _).mp h).1).2.1

/-- Forward raw protection is deliberately not invariant under all E expansions. -/
theorem erasable_partial_value :
    let t : Term Nat := .unary .fst (.binary .pair (.const .zero) bad)
    TrusteeFreeValue 0 t ∧ ¬ t.TrusteeFree 0 := by
  refine ⟨⟨.const .zero,(RootStep.fst _ _).sound,True.intro⟩,?_⟩
  exact fun h => h.2.1.2.2 rfl (.refl _)

abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []

/-- Raw published result expressions contain partials but have free values. -/
theorem raw_result_value (swap : Bool) :
    TrusteeFreeValue names.secretKey (tallyResult names swap left right [] 0) ∧
    ¬ (tallyResult names swap left right [] 0).TrusteeFree names.secretKey := by
  refine ⟨⟨.const .zero,SharedTallySPOT.nonliteral_two_candidate_tally.1 swap,True.intro⟩,?_⟩
  exact fun h => h.1.2.2 rfl (.refl _)

/-- Publicly constructed partials are allowed even inside opaque arguments. -/
theorem nested_public_initial_value (swap : Bool) :
    TrusteeFreeValue names.secretKey ((frame names swap left right).eval
      (.spk (.var 0) (.binary .partialDecrypt (.var 0) (.var 1)) (.var 1) (.var 2))) :=
  initial_recipe_trustee_free names swap left right _ (by trivial)

private def mentionsPartial : Recipe (ExpandedHandles 1) → Bool
  | .var v => decide (v=expandedPartial 0)
  | .name _ | .const _ => false
  | .unary _ a => mentionsPartial a
  | .binary _ a b => mentionsPartial a || mentionsPartial b
  | .ternary _ a b c => mentionsPartial a || mentionsPartial b || mentionsPartial c
  | .spk a b c d => mentionsPartial a || mentionsPartial b || mentionsPartial c || mentionsPartial d
private theorem result_no_partial (r : Recipe (ResultHandles 1)) :
    mentionsPartial (r.subst (fun i => .var (resultEmbedding i)))=false := by
  induction r with
  | var v => fin_cases v <;> decide
  | _ => simp_all only [Term.subst,mentionsPartial,Bool.false_or]

/-- Without minimum size, free values need not have result-only raw syntax. -/
theorem minimum_premise_required (swap : Bool) :
    let r : Recipe (ExpandedHandles 1) := .unary .fst (.binary .pair (.const .zero) (.var (expandedPartial 0)))
    TrusteeFreeValue names.secretKey ((world swap).eval r) ∧
    ¬ MinimalRecipe names.restricted (world swap).value r ∧
    ¬ ∃ s : Recipe (ResultHandles 1), r=s.subst (fun i => .var (resultEmbedding i)) := by
  dsimp only
  have he : EqE ((world swap).eval (.unary .fst (.binary .pair (.const .zero) (.var (expandedPartial 0)))))
      (.const .zero) := (RootStep.fst _ _).sound
  refine ⟨⟨.const .zero,he,True.intro⟩,?_,?_⟩
  · intro hm
    exact hm.no_smaller (s := .const .zero) trivial he (by decide)
  · rintro ⟨s,hs⟩
    have h := result_no_partial s
    rw [← hs] at h
    exact absurd h (by decide)

/-- Different honest candidates and nonliteral bit representations inhabit B8.
The final frame has all five real handles and does not collapse public names. -/
theorem final_frame_noncollapsed :
    Frame.StaticEq (finalFrame names false left right []) (finalFrame names true left right []) ∧
    (finalFrame names false left right []).eval (.var 1) ≠ (finalFrame names true left right []).eval (.var 1) ∧
    ¬ EqE ((finalFrame names true left right []).eval (.name 40)) ((finalFrame names true left right []).eval (.name 41)) := by
  refine ⟨accepted_final_staticEq names HistoricalFrameSPOT.fixture_names_fresh left right [] (by simp) trivial,
    by decide,?_⟩
  intro he
  have h := (EqE.name_iff 40 41).mp he
  omega

private theorem sequence_public : ∀ r ∈ SharedTallySPOT.submissions, r.Public SharedTallySPOT.names.restricted := by
  intro r hr
  simp only [SharedTallySPOT.submissions,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  all_goals
    apply constructorBallot_public
    · trivial
    · intro _; unfold Term.Public; decide
    · intro _; trivial
    · intro _; exact ⟨trivial,by unfold Term.Public; decide,trivial,trivial,by unfold Term.Public; decide,trivial⟩

/-- Nonempty accepted submissions, a result above one, and actual partials all
remain observable in the checked final transcript. -/
theorem nonempty_final_frame :
    Frame.StaticEq
      (finalFrame SharedTallySPOT.names false SharedTallySPOT.left SharedTallySPOT.right SharedTallySPOT.submissions)
      (finalFrame SharedTallySPOT.names true SharedTallySPOT.left SharedTallySPOT.right SharedTallySPOT.submissions) ∧
    ∀ swap, EqE (tallyResult SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right SharedTallySPOT.submissions 0)
      (.binary .add (.const .one) (.const .one)) := by
  refine ⟨accepted_final_staticEq _ NumericReflectionSPOT.fixture_names_fresh _ _ _ sequence_public
    (SharedTallySPOT.fresh_sequence_accepted false),?_⟩
  intro swap
  exact (SharedTallySPOT.fresh_sequence_tally_two.1 swap).trans
    (.binary .add (EqE.equation .zero_one) (.refl _))

/-- The new support theorem preserves a ten-node result-nonce minimum; it does
not replace the result by a larger numeral or demand old-only syntax. -/
theorem minimum_numeric_result_supported (swap : Bool) :
    ∃ s : Recipe (ResultHandles 0), ResultNonceSPOT.expanded=s.subst (fun i => .var (resultEmbedding i)) ∧
      s.nodeCount=10 := by
  have h := ResultNonceSPOT.minimum_result_nonce_tally_binding swap swap
  have hn := accepted_expanded_results_numeric ResultNonceSPOT.names NumericReflectionSPOT.fixture_names_fresh
    ResultNonceSPOT.left ResultNonceSPOT.right ResultNonceSPOT.submissions (by
      intro r hr
      simp only [ResultNonceSPOT.submissions,List.mem_cons,List.not_mem_nil,or_false] at hr
      subst r
      trivial) ResultNonceSPOT.accepted_numeric_nonce_tally.1 swap
  have hf : TrusteeFreeValue ResultNonceSPOT.names.secretKey ((ResultNonceSPOT.world swap).eval ResultNonceSPOT.expanded) :=
    (initial_recipe_trustee_free ResultNonceSPOT.names swap ResultNonceSPOT.left ResultNonceSPOT.right
      (tallyRecipe ResultNonceSPOT.submissions 0) (tallyRecipe_public _ _ _ (by
        intro r hr
        simp only [ResultNonceSPOT.submissions,List.mem_cons,List.not_mem_nil,or_false] at hr
        subst r
        trivial))).of_eq h.2.2.1.symm
  obtain ⟨s,hs⟩ := expanded_minimum_trustee_free_support _ _ _ _ _ hn _ _ h.1 hf
  refine ⟨s,hs,?_⟩
  have he := congrArg Term.nodeCount hs
  simpa only [Term.nodeCount_subst_var] using he.symm.trans h.2.1

end ExplainableCrypto.Helios.Symbolic.TrusteeFreeSPOT
