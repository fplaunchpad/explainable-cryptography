import ExplainableCrypto.Helios.Symbolic.ExpandedSuccessfulDecryptionTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedSuccessfulCheckExperiments
import ExplainableCrypto.Helios.Symbolic.ExpandedPaddedSPOT
import ExplainableCrypto.Helios.Symbolic.SuccessfulCheckSPOT

namespace ExplainableCrypto.Helios.Symbolic.ExpandedSuccessfulCheckSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []
abbrev key : Recipe (ExpandedHandles 1) := .unary .pk (.var (expandedPartial 0))
abbrev nonce : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
abbrev message : Recipe (ExpandedHandles 1) := .var (expandedResult 0)
abbrev cipher := Term.ternary .penc key nonce message
abbrev proof := Term.spk key nonce message cipher
abbrev check := Term.ternary .checkspk key cipher proof
private theorem numeric (swap : Bool) : ExpandedResultsNumeric names swap left right [] :=
  accepted_expanded_results_numeric names HistoricalFrameSPOT.fixture_names_fresh left right [] (by simp) trivial swap
private theorem valid (swap : Bool) : EqE ((world swap).eval check) (.const .ok) := by
  have hz : EqE ((world swap).eval message) (.const .zero) := by
    rw [Frame.eval,Term.subst,expanded_frame_result]
    exact (SharedTallySPOT.nonliteral_two_candidate_tally).1 swap
  have hc := EqE.ternary .penc (.refl ((world swap).eval key)) (.refl ((world swap).eval nonce)) hz
  exact (EqE.ternary .checkspk (.refl _) hc (.spk (.refl _) (.refl _) hz hc)).trans (RootStep.check_zero _ _).sound
private theorem minimum_children (swap : Bool) : Frame.MinimumChildren (world swap) check := by
  have hn := numeric swap
  have hk := expanded_minimum_pk_of_child names swap left right [] (by simp) hn (.var (expandedPartial 0)) (.of_nodeCount_one trivial rfl)
  have hr : MinimalRecipe names.restricted (world swap).value nonce := .of_nodeCount_one trivial rfl
  have hm : MinimalRecipe names.restricted (world swap).value message := .of_nodeCount_one trivial rfl
  have hc := expanded_minimum_penc_of_children names swap left right [] (by simp) hn _ _ _ hk hr hm
  exact ⟨hk,hc,expanded_minimum_spk_of_children names swap left right [] (by simp) hn _ _ _ _ hk hr hm hc⟩
private theorem diagonal (swap : Bool) (bound : Nat) : Frame.SharedMinimaBelow (world swap) (world swap) bound := by
  intro r hp _
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (world swap).value) r hp
  exact ⟨m,hm,he,he⟩

/-- Actual partials supply the key and nonce, and a published zero supplies the
payload. The 18-node check has minimum children and shares one-node ok between
different-vote worlds. The new local theorem has an inhabited diagonal instance. -/
theorem published_constructed_check (swap swap' : Bool) :
    Frame.MinimumChildren (world swap) check ∧ check.nodeCount=18 ∧
    ¬ MinimalRecipe names.restricted (world swap).value check ∧
    Frame.SharedMinimum (world swap) (world swap') check ∧
    Frame.SharedMinimum (world swap) (world swap) check := by
  have hc := minimum_children swap
  refine ⟨hc,rfl,?_,⟨.const .ok,.of_nodeCount_one trivial rfl,valid swap,valid swap'⟩,?_⟩
  · intro hm
    exact hm.no_smaller (s := .const .ok) trivial (valid swap) (by decide)
  · exact accepted_expanded_minimum_children_check_shared_of_two_way_minima names HistoricalFrameSPOT.fixture_names_fresh
      swap swap left right [] (by simp) trivial _ _ _ hc.1 hc.2.1 hc.2.2 (diagonal swap _) (diagonal swap _)

/-- With an actual published partial as key, changing only the proof's fourth
argument nonce rejects the check. Matching the first three fields is insufficient. -/
theorem wrong_binding_with_published_key (swap : Bool) :
    let k : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
    let c := Term.ternary .penc k (.name 40) (.const .zero)
    ¬ EqE ((world swap).eval (.ternary .checkspk k c
      (.spk k (.name 40) (.const .zero) (.ternary .penc k (.name 41) (.const .zero))))) (.const .ok) := by
  dsimp only
  intro he
  obtain ⟨_,_,_,_,hp⟩ := (EqE.check_ok_iff_components _ _ _).mp he
  have h := (EqE.name_iff 41 40).mp
    ((EqE.penc_iff _ _ _ _ _ _).mp ((EqE.spk_iff _ _ _ _ _ _ _ _).mp hp).2.2.2).2.1
  omega

/-- A real accepted nonempty submission sequence publishes two. Cheapness of
its one-node handle does not make that payload a bit accepted by proof checking. -/
theorem published_two_rejected (swap : Bool) :
    let φ := expandedFrame SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right SharedTallySPOT.submissions
    let m : Recipe (ExpandedHandles 0) := .var (expandedResult 0)
    let c := Term.ternary .penc (.name 40) (.name 41) m
    ¬ EqE (φ.eval (.ternary .checkspk (.name 40) c (.spk (.name 40) (.name 41) m c))) (.const .ok) := by
  dsimp only
  intro he
  obtain ⟨_,bit,hbit,_,hp⟩ := (EqE.check_ok_iff_components _ _ _).mp he
  have hm := ((EqE.spk_iff _ _ _ _ _ _ _ _).mp hp).2.2.1
  have ht := (ExpandedPaddedSPOT.accepted_published_two_is_cheap swap).1
  have hb := (irreducible_eqE_iff_base (addNumeral_irreducible 2) (constant_irreducible bit)).mp (ht.symm.trans hm)
  have hn := congrArg AddSummary.numeric hb.add_summary
  rcases hbit with rfl | rfl <;> exact absurd hn (by decide)

/-- Both voters' honest component and aggregate checks remain valid with all
published handles present and reducible candidate representatives. -/
theorem honest_checks (swap : Bool) (i : Fin 2) (j : Fin 2) :
    EqE ((world swap).eval (.ternary .checkspk (.var (expandedOld 0))
      (combinationRecipeWith expandedOld (.leaf (i,j))) ((Term.var (expandedOld i.succ)).project (2+j.val)))) (.const .ok) ∧
    EqE ((world swap).eval (.ternary .checkspk (.var (expandedOld 0))
      (combinationRecipeWith expandedOld (voterCombination (n := 1) i)) ((Term.var (expandedOld i.succ)).project 4))) (.const .ok) :=
  ⟨expanded_honest_component_check_recipe_valid names swap left right [] i j,
   expanded_honest_aggregate_check_recipe_valid names swap left right [] i⟩

/-- A commuted honest aggregate has a distinct recipe but the exact same
minimum indexed occurrences. The new origin theorem gives recipe equality,
which validates the bound aggregate check after either candidate assignment. -/
theorem commuted_aggregate_binding (swap swap' : Bool) :
    let t : Combination (HonestIndex 1) := .mul (.leaf (0,1)) (.leaf (0,0))
    let r := combinationRecipeWith (handles := ExpandedHandles 1) expandedOld t
    let a := combinationRecipeWith (handles := ExpandedHandles 1) expandedOld (voterCombination (n := 1) 0)
    r ≠ a ∧ MinimalRecipe names.restricted (world swap).value r ∧ EqE r a ∧
    EqE ((world swap').eval (.ternary .checkspk (.var (expandedOld 0)) r ((Term.var (expandedOld 1)).project 4))) (.const .ok) := by
  let t : Combination (HonestIndex 1) := .mul (.leaf (0,1)) (.leaf (0,0))
  let r := combinationRecipeWith (handles := ExpandedHandles 1) expandedOld t
  let a := combinationRecipeWith (handles := ExpandedHandles 1) expandedOld (voterCombination (n := 1) 0)
  have hm := accepted_expanded_minimum_honest_combination names HistoricalFrameSPOT.fixture_names_fresh swap left right [] (by simp) trivial t
  have hraw : BaseEq r a := .equation (.comm .mul trivial _ _)
  have he := expanded_minimum_honest_combination_recipe_eqE names HistoricalFrameSPOT.fixture_names_fresh swap left right []
    (by simp) (numeric swap) r hm (voterCombination 0) (hraw.sound.subst _)
  exact ⟨by decide,hm,he,(EqE.ternary .checkspk (.refl _) (he.subst _) (.refl _)).trans
    (expanded_honest_aggregate_check_recipe_valid names swap' left right [] 0)⟩

/-- Retaining the five-candidate aggregate costs 24 nodes in the expanded
presentation too; its self-comparison exceeds the 38-node check's strict bound. -/
theorem aggregate_comparison_exceeds_bound :
    let a := combinationRecipeWith (handles := ExpandedHandles 4) expandedOld (voterCombination (n := 4) 0)
    let c := (Term.var (expandedOld 1) : Recipe (ExpandedHandles 4)).project 10
    a.nodeCount=24 ∧ (Term.ternary .checkspk (.var (expandedOld 0)) a c).nodeCount=38 ∧
    ¬ a.nodeCount+a.nodeCount < (Term.ternary .checkspk (.var (expandedOld 0)) a c).nodeCount := by decide

/-- The longer one-candidate aggregate proof is still a valid alias after
publication; no claim that this longer selector is minimum is needed. -/
theorem one_candidate_alias (swap : Bool) :
    let φ := expandedFrame ProofObservationSPOT.oneNames swap ProofObservationSPOT.oneLeft ProofObservationSPOT.oneRight []
    let a := (Term.var (expandedOld 1) : Recipe (ExpandedHandles 0)).project 1
    let b := (Term.var (expandedOld 1) : Recipe (ExpandedHandles 0)).project 2
    a ≠ b ∧ EqE (φ.eval a) (φ.eval b) ∧
    EqE (φ.eval (.ternary .checkspk (.var (expandedOld 0))
      (combinationRecipeWith expandedOld (voterCombination (n := 0) 0)) b)) (.const .ok) := by
  refine ⟨by decide,?_,expanded_honest_aggregate_check_recipe_valid _ swap _ _ [] 0⟩
  simpa only [Frame.eval,Term.subst_project,Term.subst,expanded_frame_old] using
    (ProofObservationSPOT.one_candidate_fields_coincide swap).2

/-- Minimum atomic children in arbitrary frames still do not force checking
success to transfer. The historical and smaller-observation premises matter. -/
theorem arbitrary_frame_transfer_refuted :
    Frame.MinimumChildren (MinimumDestructorSPOT.probeFrame true) MinimumDestructorSPOT.probe ∧
    EqE ((MinimumDestructorSPOT.probeFrame true).eval MinimumDestructorSPOT.probe) (.const .ok) ∧
    ¬ EqE ((MinimumDestructorSPOT.probeFrame false).eval MinimumDestructorSPOT.probe) (.const .ok) :=
  SuccessfulCheckSPOT.arbitrary_frame_success_does_not_transfer

/-- The reduced successful-decryption interface has actual equal-candidate
instances; these yield all three static-equivalence presentations conditionally. -/
theorem decryption_pipeline_inhabited :
    let φ := expandedFrame names false left left []
    let ψ := expandedFrame names true left left []
    Frame.SuccessfulDecryptionTransport φ ψ ∧ Frame.SuccessfulDecryptionTransport ψ φ ∧
    Frame.StaticEq φ ψ ∧
    Frame.StaticEq (partialFrame names false left left []) (partialFrame names true left left []) ∧
    Frame.StaticEq (finalFrame names false left left []) (finalFrame names true left left []) := by
  have h : Frame.SuccessfulDecryptionTransport (expandedFrame names false left left []) (expandedFrame names true left left []) := by
    intro r hp _ _ _ _ _
    obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (expandedFrame names false left left []).value) r hp
    exact ⟨m,hm,he,he⟩
  exact ⟨h,h,
    accepted_expanded_staticEq_of_successful_decryption_transport names HistoricalFrameSPOT.fixture_names_fresh left left [] (by simp) trivial h h,
    accepted_partial_staticEq_of_successful_decryption_transport names HistoricalFrameSPOT.fixture_names_fresh left left [] (by simp) trivial h h,
    accepted_final_staticEq_of_successful_decryption_transport names HistoricalFrameSPOT.fixture_names_fresh left left [] (by simp) trivial h h⟩

end ExplainableCrypto.Helios.Symbolic.ExpandedSuccessfulCheckSPOT
