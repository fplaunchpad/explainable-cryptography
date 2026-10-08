import ExplainableCrypto.Helios.Symbolic.ExpandedHonestMinima
import ExplainableCrypto.Helios.Symbolic.ExpandedHonestExperiments
import ExplainableCrypto.Helios.Symbolic.ExpandedConstructedSPOT

namespace ExplainableCrypto.Helios.Symbolic.ExpandedHonestSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []
abbrev first : Combination (HonestIndex 1) := .mul (.leaf (0,1)) (.mul (.leaf (1,0)) (.leaf (0,1)))
abbrev second : Combination (HonestIndex 1) := .mul (.mul (.leaf (0,1)) (.leaf (0,1))) (.leaf (1,0))
abbrev repeated : Combination (HonestIndex 1) := .mul (.leaf (0,0)) (.leaf (0,0))
abbrev recipe (a : Combination (HonestIndex 1)) := combinationRecipeWith (handles := ExpandedHandles 1) expandedOld a
private theorem numeric (swap : Bool) : ExpandedResultsNumeric names swap left right [] :=
  accepted_expanded_results_numeric names HistoricalFrameSPOT.fixture_names_fresh left right [] (by simp) trivial swap
private theorem minimum (swap : Bool) (a : Combination (HonestIndex 1)) :
    MinimalRecipe names.restricted (world swap).value (recipe a) :=
  accepted_expanded_minimum_honest_combination names HistoricalFrameSPOT.fixture_names_fresh swap left right [] (by simp) trivial a

/-- Three selectors cost 3+2+3 plus two multiplication nodes. Reassociation
retains ten nodes, global minimum size and shared syntax with different votes. -/
theorem indexed_reassociation_minimum (swap swap' : Bool) :
    MinimalRecipe names.restricted (world swap).value (recipe first) ∧
    MinimalRecipe names.restricted (world swap).value (recipe second) ∧
    recipe first ≠ recipe second ∧ BaseEq (recipe first) (recipe second) ∧
    (recipe first).nodeCount = 10 ∧
    Frame.SharedMinimum (world swap) (world swap') (recipe first) := by
  have hi : first.indices = second.indices := by simp only [Combination.indices]; ac_rfl
  have he := Combination.evaluate_baseEq_of_indices .mul trivial
    (fun i : HonestIndex 1 => (Term.var (expandedOld i.1.succ) : Recipe (ExpandedHandles 1)).project i.2.val) hi
  exact ⟨minimum swap first,minimum swap second,by decide,he,rfl,
    expanded_honest_combination_shared names HistoricalFrameSPOT.fixture_names_fresh swap left right []
      (by simp) (numeric swap) first _⟩

/-- Two occurrences cost five nodes and cannot collapse to one selector. -/
theorem duplicate_occurrences_required (swap : Bool) :
    MinimalRecipe names.restricted (world swap).value (recipe repeated) ∧
    (recipe repeated).nodeCount = 5 ∧
    ¬ EqE ((world swap).eval (recipe repeated)) ((world swap).eval (recipe (.leaf (0,0)))) := by
  refine ⟨minimum swap repeated,rfl,?_⟩
  intro he
  exact (minimum swap repeated).no_smaller (combinationRecipeWith_public _ _ _) he (by decide)

/-- Arbitrary globally minimum competitors, including all new-handle recipes,
retain the exact three indexed occurrences and the independently counted ten nodes. -/
theorem competitor_origin_and_cost (swap : Bool) (r : Recipe (ExpandedHandles 1))
    (hm : MinimalRecipe names.restricted (world swap).value r)
    (he : EqE ((world swap).eval r) ((world swap).eval (recipe first))) :
    (∃ a, r = recipe a ∧ a.indices = first.indices) ∧ r.nodeCount = 10 := by
  obtain ⟨a,ha,hi⟩ := expanded_minimum_honest_combination_origin names HistoricalFrameSPOT.fixture_names_fresh
    swap left right [] (by simp) (numeric swap) r hm first he
  refine ⟨⟨a,ha,hi⟩,?_⟩
  rw [ha]
  rw [combinationRecipeWith_nodeCount,combinationRecipe_nodeCount_eq hi]
  rfl

/-- No published or retained whole handle aliases even the cheapest honest
selector. The global minimum conclusion quantifies over all public competitors. -/
theorem no_whole_handle_alias (swap : Bool) (v : Fin (ExpandedHandles 1)) :
    (recipe (.leaf (0,0))).nodeCount = 2 ∧
    ¬ EqE ((world swap).eval (recipe (.leaf (0,0)))) ((world swap).eval (.var v)) := by
  refine ⟨rfl,?_⟩
  intro he
  exact (minimum swap (.leaf (0,0))).no_smaller (s := .var v) trivial he (by simp [Term.nodeCount]; decide)

/-- Nonempty accepted submissions publish a tally of two. Honest selector
combinations still retain their full eight-node minimum in both assignments. -/
theorem accepted_nonempty_submissions (swap : Bool) :
    let a : Combination (HonestIndex 0) := .mul (.leaf (0,0)) (.mul (.leaf (1,0)) (.leaf (0,0)))
    let φ := expandedFrame SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right SharedTallySPOT.submissions
    MinimalRecipe SharedTallySPOT.names.restricted φ.value (combinationRecipeWith expandedOld a) ∧
      (combinationRecipeWith (handles := ExpandedHandles 0) expandedOld a).nodeCount = 8 := by
  have hpub : ∀ r ∈ SharedTallySPOT.submissions, r.Public SharedTallySPOT.names.restricted := by
    intro r hr
    simp only [SharedTallySPOT.submissions,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    all_goals
      apply constructorBallot_public
      · trivial
      · intro _; simp only [Term.Public]; decide
      · intro _; trivial
      · intro _; exact ⟨trivial,by simp only [Term.Public]; decide,trivial,trivial,by simp only [Term.Public]; decide,trivial⟩
  exact ⟨accepted_expanded_minimum_honest_combination SharedTallySPOT.names NumericReflectionSPOT.fixture_names_fresh
    swap SharedTallySPOT.left SharedTallySPOT.right SharedTallySPOT.submissions hpub (SharedTallySPOT.fresh_sequence_accepted false) _,rfl⟩

/-- Colliding nonces allow a three-node selector to equal a two-node one,
including in the expanded frame. Freshness remains load-bearing. -/
theorem nonce_freshness_required (swap : Bool) :
    ¬ ProofObservationSPOT.colliding.Fresh ∧
    ¬ MinimalRecipe ProofObservationSPOT.colliding.restricted
      (expandedFrame ProofObservationSPOT.colliding swap right right []).value (recipe (.leaf (0,1))) := by
  let ns := ProofObservationSPOT.colliding
  have he : EqE ((expandedFrame ns swap right right []).eval (recipe (.leaf (0,1))))
      ((expandedFrame ns swap right right []).eval (recipe (.leaf (0,0)))) := by
    cases swap with
    | false =>
      exact (expanded_combination_value ns false right right [] (.leaf (0,1))).trans
        (expanded_combination_value ns false right right [] (.leaf (0,0))).symm
    | true =>
      exact (expanded_combination_value ns true right right [] (.leaf (0,1))).trans
        (expanded_combination_value ns true right right [] (.leaf (0,0))).symm
  exact ⟨ProofObservationSPOT.freshness_required.2,
    fun hm => hm.no_smaller (combinationRecipeWith_public _ _ _) he (by decide)⟩

def publishedCiphertextFrame : Frame names.restricted (ExpandedHandles 1) :=
  ⟨fun i => if i = expandedResult 0 then (world false).eval (recipe repeated) else (world false).value i⟩

/-- Replacing a result slot with the honest ciphertext product invalidates
minimum size. The actual published-value hypotheses cannot be dropped. -/
theorem arbitrary_publication_invalidates_minimum :
    MinimalRecipe names.restricted (world false).value (recipe repeated) ∧
    ¬ MinimalRecipe names.restricted publishedCiphertextFrame.value (recipe repeated) := by
  refine ⟨minimum false repeated,?_⟩
  intro hm
  have he : EqE (publishedCiphertextFrame.eval (recipe repeated))
      (publishedCiphertextFrame.eval (.var (expandedResult 0))) := .refl _
  exact hm.no_smaller (s := .var (expandedResult 0)) trivial he (by decide)

/-- A concrete nine-node nonminimum product of four-node minimum constructors
inhabits the exact remaining-product classification in the expanded frame. -/
theorem nonminimum_product_has_public_contribution (swap : Bool) :
    ∃ u v : CiphertextAssembly 1 (ExpandedHandles 1),
      u.recipeWith expandedOld = ExpandedConstructedSPOT.a.recipeWith expandedOld ∧
      v.recipeWith expandedOld = ExpandedConstructedSPOT.b.recipeWith expandedOld ∧
      ((u.mul v).recipeWith expandedOld).Public names.restricted ∧
      ((∃ r p, (u.mul v).group = .constructed r p) ∨ (∃ r p a, (u.mul v).group = .mixed r p a)) := by
  have ha : MinimalRecipe names.restricted (world swap).value (ExpandedConstructedSPOT.a.recipeWith expandedOld) :=
    accepted_expanded_minimum_penc_of_children names HistoricalFrameSPOT.fixture_names_fresh swap left right []
      (by simp) trivial _ _ _ (.of_nodeCount_one trivial rfl) (.of_nodeCount_one trivial rfl) (.of_nodeCount_one trivial rfl)
  have hb : MinimalRecipe names.restricted (world swap).value (ExpandedConstructedSPOT.b.recipeWith expandedOld) :=
    accepted_expanded_minimum_penc_of_children names HistoricalFrameSPOT.fixture_names_fresh swap left right []
      (by simp) trivial _ _ _ (.of_nodeCount_one trivial rfl) (.of_nodeCount_one trivial rfl) (.of_nodeCount_one trivial rfl)
  have hn := (ExpandedConstructedSPOT.repeated_nonce_shared_compression swap swap).2.2.2.2.2
  exact expanded_nonminimum_ciphertext_product_public_group names HistoricalFrameSPOT.fixture_names_fresh swap left right []
    (by simp) (numeric swap) _ _ ha hb hn ⟨_,_,_,(RootStep.homomorphic _ _ _ _ _).sound⟩

end ExplainableCrypto.Helios.Symbolic.ExpandedHonestSPOT
