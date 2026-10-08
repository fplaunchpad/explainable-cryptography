import ExplainableCrypto.Helios.Symbolic.ExpandedCompositionTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedStuckSPOT
import ExplainableCrypto.Helios.Symbolic.ExpandedCompositionExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedCompositionSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []

private theorem numeric (swap : Bool) (l r : CandidateSubstitution 1 Empty) : ExpandedResultsNumeric names swap l r [] :=
  accepted_expanded_results_numeric names HistoricalFrameSPOT.fixture_names_fresh l r [] (by simp) trivial swap

/-- Every actual handle, including all new publication slots, is a semantic
composition atom in either assignment. -/
theorem all_handles_noncomposition (swap : Bool) (v : Fin (ExpandedHandles 1)) (x y : Ground) :
    ¬ EqE ((world swap).eval (.var v)) (.binary .compose x y) :=
  expanded_handle_not_composition names swap left right [] (numeric swap left right) v x y

/-- Two one-node published children yield an actual minimum composition. -/
theorem published_children_compose_minimum (swap : Bool) :
    MinimalRecipe names.restricted (world swap).value
      (.binary .compose (.var (expandedPartial 0)) (.var (expandedResult 1))) :=
  expanded_minimum_compose_of_children names swap left right [] (numeric swap left right) names.restricted _ _
    (.of_nodeCount_one trivial rfl) (.of_nodeCount_one trivial rfl)

/-- Even a zero-valued result cannot become a composition unit or an
idempotent factor: both occurrences contribute to minimum size. -/
theorem duplicate_result_factors_do_not_collapse (swap : Bool) :
    let a : Recipe (ExpandedHandles 1) := .var (expandedResult 0)
    MinimalRecipe names.restricted (world swap).value (.binary .compose a a) ∧
    ¬ EqE ((world swap).eval (.binary .compose a a)) ((world swap).eval a) := by
  let a : Recipe (ExpandedHandles 1) := .var (expandedResult 0)
  have hm := expanded_minimum_compose_of_children names swap left right [] (numeric swap left right) names.restricted a a
    (.of_nodeCount_one trivial rfl) (.of_nodeCount_one trivial rfl)
  refine ⟨hm,?_⟩
  intro he
  have h := hm.least a trivial he
  change 3 ≤ 1 at h
  omega

/-- Reassociation/permutation of three published occurrences instantiates the
accepted equality theorem. A diagonal election supplies smaller observations. -/
theorem accepted_reassociated_published_comparison :
    let φ := expandedFrame names false left left []
    let ψ := expandedFrame names true left left []
    let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
    let b : Recipe (ExpandedHandles 1) := .var (expandedResult 1)
    let r := Term.binary .compose a (.binary .compose b a)
    let s := Term.binary .compose (.binary .compose a a) b
    (EqE (φ.eval r) (φ.eval s) ↔ EqE (ψ.eval r) (ψ.eval s)) ∧ EqE (φ.eval r) (φ.eval s) := by
  let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
  let b : Recipe (ExpandedHandles 1) := .var (expandedResult 1)
  have ha : MinimalRecipe names.restricted (expandedFrame names false left left []).value a := .of_nodeCount_one trivial rfl
  have hb : MinimalRecipe names.restricted (expandedFrame names false left left []).value b := .of_nodeCount_one trivial rfl
  have close := expanded_minimum_compose_of_children names false left left [] (numeric false left left) names.restricted
  have hr := close a (.binary .compose b a) ha (close b a hb ha)
  have hs := close (.binary .compose a a) b (close a a ha ha) hb
  refine ⟨accepted_expanded_minimum_composition_equality_swap names HistoricalFrameSPOT.fixture_names_fresh
    false true left left [] (by simp) trivial _ _ hr hs (.refl _) (.refl _) (fun _ _ _ _ _ => Iff.rfl),?_⟩
  exact (EqE.binary .compose (.refl _) (.equation (.comm .compose trivial _ _))).trans
    (EqE.equation (.assoc .compose trivial _ _ _)).symm

/-- A raw projection leaf can hide two composition factors. Its value and
nonminimum size are both exposed, preserving the minimized gate mutation. -/
theorem hidden_projection_requires_minimum (swap : Bool) :
    let c : Recipe (ExpandedHandles 1) := .binary .compose (.name 40) (.name 41)
    let r := Term.unary .fst (.binary .pair c (.name 50))
    EqE ((world swap).eval r) ((world swap).eval c) ∧
    ¬ MinimalRecipe names.restricted (world swap).value r ∧
    ¬ (∃ a b, r = .binary .compose a b) ∧ r.composeLeaves.card = 1 ∧ c.composeLeaves.card = 2 := by
  refine ⟨.equation (.fst _ _),?_,?_,by decide,by decide⟩
  · intro hm
    exact hm.raw_irreducible _ (RootStep.fst _ _).to_rewrite
  · rintro ⟨a,b,h⟩
    cases h

/-- Published partials remain valid E5 secrets for newly built ciphertexts.
An E5 wrapper exposing composition is nonminimum, so its raw origin is excluded. -/
theorem E5_exposes_composition (swap : Bool) :
    let key : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
    let c : Recipe (ExpandedHandles 1) := .binary .compose (.name 40) (.name 41)
    let r := Term.binary .dec key (keyCiphertext key (.name 50) c)
    EqE ((world swap).eval r) ((world swap).eval c) ∧
    ¬ MinimalRecipe names.restricted (world swap).value r := by
  refine ⟨(RootStep.decrypt _ _ _).sound,?_⟩
  intro hm
  exact hm.raw_irreducible _ (RootStep.decrypt _ _ _).to_rewrite

/-- Actual E6 succeeds and returns the independently expected numeric one,
which has no composition value under full E. -/
theorem E6_numeric_output_not_composition (swap : Bool) :
    (∃ out, DecryptionMatch (tallyPartial names swap left right [] 1) (tallyCiphertext names swap left right [] 1) out) ∧
    EqE (tallyResult names swap left right [] 1) (.const .one) ∧
    ∀ x y, ¬ EqE (tallyResult names swap left right [] 1) (.binary .compose x y) := by
  refine ⟨(TrusteePartialSPOT.both_candidates_match swap 1).1,SharedTallySPOT.nonliteral_two_candidate_tally.2 swap,?_⟩
  obtain ⟨number,hnum⟩ := numeric swap left right 1
  intro x y he
  exact numeric_not_composition number x y (hnum.symm.trans he)

/-- Arbitrary frames need not satisfy the composition-handle exclusion.
Publishing a composition at size one defeats constructor minimum closure. -/
theorem arbitrary_composition_handle_breaks_minimum_closure :
    let φ : Frame ∅ 1 := ⟨fun _ => .binary .compose (.name 40) (.name 41)⟩
    MinimalRecipe ∅ φ.value (.name 40) ∧ MinimalRecipe ∅ φ.value (.name 41) ∧
    ¬ MinimalRecipe ∅ φ.value (.binary .compose (.name 40) (.name 41)) := by
  refine ⟨.of_nodeCount_one (by simp [Term.Public]) rfl,.of_nodeCount_one (by simp [Term.Public]) rfl,?_⟩
  intro hm
  have h := hm.least (.var 0) trivial (.refl _)
  change 3 ≤ 1 at h
  omega

end ExplainableCrypto.Helios.Symbolic.ExpandedCompositionSPOT
