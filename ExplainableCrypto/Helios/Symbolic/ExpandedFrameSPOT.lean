import ExplainableCrypto.Helios.Symbolic.ExpandedMinimumOrigins
import ExplainableCrypto.Helios.Symbolic.ExpandedFrameExperiments
import ExplainableCrypto.Helios.Symbolic.PublishedFrameSPOT

namespace ExplainableCrypto.Helios.Symbolic.ExpandedFrameSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []

/-- Every slot of both actual presentations is reconstructed, including both
nonliteral candidates and the complete original tuples. -/
theorem both_presentations_reconstruct (swap : Bool) :
    (∀ i, EqE ((finalFrame names swap left right []).eval (expandedRecipes i)) ((world swap).value i)) ∧
    (∀ i, EqE ((world swap).eval (tupleRecipes i)) ((finalFrame names swap left right []).value i)) :=
  ⟨expandedRecipes_value names swap left right [],tupleRecipes_value names swap left right []⟩

/-- The two result slots have independently known unequal values; shifting
candidate one's index to candidate zero changes a public observation. -/
theorem result_slots_distinct (swap : Bool) :
    EqE ((world swap).value (expandedResult 0)) (.const .zero) ∧
    EqE ((world swap).value (expandedResult 1)) (.const .one) ∧
    ¬ EqE ((world swap).value (expandedResult 0)) ((world swap).value (expandedResult 1)) := by
  have hzero : EqE ((world swap).value (expandedResult 0)) (.const .zero) := by
    rw [expanded_frame_result]
    exact SharedTallySPOT.nonliteral_two_candidate_tally.1 swap
  have hone : EqE ((world swap).value (expandedResult 1)) (.const .one) := by
    rw [expanded_frame_result]
    exact SharedTallySPOT.nonliteral_two_candidate_tally.2 swap
  exact ⟨hzero,hone,fun h => zero_not_one (hzero.symm.trans (h.trans hone))⟩

/-- Omitting a partial cannot reconstruct the original complete tuple under E. -/
theorem missing_partial_is_observable :
    ¬ EqE (Term.tuple [(world false).value (expandedPartial 0)])
      ((finalFrame names false left right []).value 3) := by
  rw [expanded_frame_partial]
  exact PublishedFrameSPOT.omitted_partial_slot_observable

/-- A published partial has a minimum handle recipe, and the general origin
classification permits only partial slots for every other minimum recipe of its value. -/
theorem minimum_partial_origin (swap : Bool) (j : Fin 2)
    (r : Recipe (ExpandedHandles 1)) (hr : MinimalRecipe names.restricted (world swap).value r)
    (he : EqE ((world swap).eval r) (tallyPartial names swap left right [] j)) :
    MinimalRecipe names.restricted (world swap).value (.var (expandedPartial j)) ∧
    ∃ i, r = .var (expandedPartial i) ∧
      EqE (tallyCiphertext names swap left right [] i) (tallyCiphertext names swap left right [] j) :=
  ⟨.of_nodeCount_one trivial rfl,
    expanded_minimum_trustee_partial_origin names HistoricalFrameSPOT.fixture_names_fresh
      left right [] (by simp) trivial swap j r hr he⟩

/-- Removing minimum size admits a wrapper with the same partial value but
no partial-handle syntax. -/
theorem minimum_premise_required (swap : Bool) :
    let r : Recipe (ExpandedHandles 1) := .unary .fst (.binary .pair (.var (expandedPartial 0)) (.name 90))
    EqE ((world swap).eval r) (tallyPartial names swap left right [] 0) ∧
      ¬ (∃ i : Fin 2, r = .var (expandedPartial i)) := by
  refine ⟨?_,?_⟩
  · have he : EqE ((world swap).eval (.unary .fst (.binary .pair (.var (expandedPartial 0)) (.name 90))))
        ((world swap).value (expandedPartial 0)) := (RootStep.fst _ _).sound
    simpa only [expanded_frame_partial] using he
  · rintro ⟨i,hi⟩
    cases hi

/-- An actual tally probe still computes one, but cannot be minimum now that
its exact result has an individual public handle. -/
theorem tally_decryption_has_shortcut (swap : Bool) :
    let r := (tallyRecipe [] (1 : Fin 2)).subst (fun i => Term.var (expandedOld i))
    EqE ((world swap).eval (.binary .dec (.var (expandedPartial 1)) r)) (.const .one) ∧
      ¬ MinimalRecipe names.restricted (world swap).value (.binary .dec (.var (expandedPartial 1)) r) := by
  let r := (tallyRecipe [] (1 : Fin 2)).subst (fun i => Term.var (expandedOld (n := 1) i))
  have ha : EqE ((world swap).eval (.var (expandedPartial 1))) (tallyPartial names swap left right [] 1) := by
    simp only [Frame.eval,Term.subst,expanded_frame_partial]
    exact .refl _
  have hb : EqE ((world swap).eval r) (tallyCiphertext names swap left right [] 1) := by
    rw [show (world swap).eval r = (frame names swap left right).eval (tallyRecipe [] (1 : Fin 2)) from
      expanded_old_recipe_value names swap left right [] _]
    exact .refl _
  exact ⟨(EqE.binary .dec ha hb).trans (SharedTallySPOT.nonliteral_two_candidate_tally.2 swap),
    expanded_bound_tally_decryption_not_minimal names swap left right [] 1 _ _ ha hb⟩

/-- The nonempty fixture publishes the tally two in a minimum one-node recipe,
although its explicit numeric syntax contains five nodes. -/
theorem nonempty_result_has_one_node (swap : Bool) :
    let φ := expandedFrame ProofObservationSPOT.oneNames swap ProofObservationSPOT.oneLeft
      ProofObservationSPOT.oneRight SharedTallySPOT.submissions
    let r : Recipe (ExpandedHandles 0) := .var (expandedResult 0)
    MinimalRecipe ProofObservationSPOT.oneNames.restricted φ.value r ∧
      EqE (φ.eval r) (addNumeral 2) ∧ (addNumeral (V := Empty) 2).nodeCount = 5 := by
  refine ⟨.of_nodeCount_one trivial rfl,?_,rfl⟩
  simp only [Frame.eval,Term.subst,expanded_frame_result]
  exact SharedTallySPOT.fresh_sequence_tally_two.1 swap

/-- Public translations preserve values but not syntax costs. -/
theorem presentation_costs_differ (swap : Bool) :
    ((Term.var 3 : Recipe 5).project 0).nodeCount = 2 ∧
    (Term.var (expandedPartial (n := 1) 0) : Recipe (ExpandedHandles 1)).nodeCount = 1 ∧
    EqE ((finalFrame names swap left right []).eval ((Term.var 3).project 0))
      ((world swap).eval (.var (expandedPartial 0))) := by
  refine ⟨rfl,rfl,?_⟩
  simp only [Frame.eval,Term.subst,expanded_frame_partial]
  exact finalFrame_partial_project names swap left right [] 0

/-- The changed presentation still permits public structured-key E5, and its
name invariant does not force computations to get stuck. -/
theorem new_key_decryption_preserved (swap : Bool) :
    let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
    let r := Term.binary .dec a (keyCiphertext a (.name 60) (.name 90))
    r.Public names.restricted ∧ EqE ((world swap).eval r) (.name 90) ∧
      (world swap).OpaqueProtected := by
  refine ⟨?_,(RootStep.decrypt _ _ _).sound,expanded_frame_opaque_protected names swap left right [] (by simp)⟩
  change True ∧ True ∧ 60 ∉ names.restricted ∧ 90 ∉ names.restricted
  decide

/-- The exact criterion has an inhabited diagonal case with distinct public
names. Its different-vote equivalence premise is still unproved. -/
theorem criterion_diagonal :
    Frame.StaticEq (expandedFrame names false left left []) (expandedFrame names true left left []) ∧
    ¬ EqE ((expandedFrame names true left left []).eval (.name 40))
      ((expandedFrame names true left left []).eval (.name 41)) := by
  refine ⟨(expanded_frame_staticEq_iff_partial names left left [] (by simp)).mpr (Frame.StaticEq.refl _),?_⟩
  intro he
  exact absurd ((EqE.name_iff 40 41).mp he) (by decide)

end ExplainableCrypto.Helios.Symbolic.ExpandedFrameSPOT
