import ExplainableCrypto.Helios.Symbolic.SuccessfulDecryptionTransport
import ExplainableCrypto.Helios.Symbolic.PaddedMinimumSPOT

namespace ExplainableCrypto.Helios.Symbolic.SuccessfulCheckSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world := LocalRootSPOT.world
abbrev cipher : Recipe 3 := .ternary .penc (.name 40) (.name 41) (.const .zero)
abbrev proof : Recipe 3 := .spk (.name 40) (.name 41) (.const .zero) cipher
abbrev check : Recipe 3 := .ternary .checkspk (.name 40) cipher proof
abbrev wrap (r : Recipe 3) : Recipe 3 := .unary .fst (.binary .pair r (.const .bottom))

private theorem public40 : (Term.name 40 : Recipe 3).Public names.restricted := by
  change 40 ∉ names.restricted; decide
private theorem public41 : (Term.name 41 : Recipe 3).Public names.restricted := by
  change 41 ∉ names.restricted; decide
private theorem diagonal (swap : Bool) (bound : Nat) :
    Frame.SharedMinimaBelow (world swap) (world swap) bound := by
  intro r hp _
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (world swap).value) r hp
  exact ⟨m,hm,he,he⟩

/-- Actual minimum children enter the successful branch. The whole check
is fourteen nodes, reduces to ok, and is not itself minimum. -/
theorem constructed_check_discharged (swap : Bool) :
    Frame.MinimumChildren (world swap) check ∧ check.nodeCount=14 ∧
    ¬ MinimalRecipe names.restricted (world swap).value check ∧
    Frame.SharedMinimum (world swap) (world swap) check ∧
    ¬ Frame.SuccessfulDecryptionCase (world swap) check := by
  have hk : MinimalRecipe names.restricted (world swap).value (.name 40) := .of_nodeCount_one public40 rfl
  have hr : MinimalRecipe names.restricted (world swap).value (.name 41) := .of_nodeCount_one public41 rfl
  have hz : MinimalRecipe names.restricted (world swap).value (.const .zero) := .of_nodeCount_one trivial rfl
  have hc := minimum_penc_of_children names swap left right _ _ _ hk hr hz
  have hp := minimum_spk_of_children names swap left right _ _ _ _ hk hr hz hc
  refine ⟨⟨hk,hc,hp⟩,rfl,?_,minimum_children_check_shared_of_two_way_minima names
    HistoricalFrameSPOT.fixture_names_fresh swap swap left right _ _ _ hk hc hp
    (diagonal swap _) (diagonal swap _),not_false⟩
  intro hm
  exact hm.no_smaller (s := .const .ok) trivial (RootStep.check_zero _ _).sound (by decide)

/-- Removable wrappers exercise all four comparisons of constructed transfer.
The encryption-shape test has exactly the proof's size, below its parent. -/
theorem wrapped_constructed_transfer (swap : Bool) :
    let p := Term.spk (wrap (.name 40)) (.name 41) (wrap (.const .zero)) (wrap cipher)
    let t := Term.ternary .checkspk (wrap (.name 40)) (wrap cipher) p
    (wrap cipher).nodeCount + (Term.ternary .penc (wrap (.name 40)) (.name 41)
      (wrap (.const .zero))).nodeCount = p.nodeCount ∧
    p.nodeCount < t.nodeCount ∧ EqE ((world swap).eval t) (.const .ok) := by
  refine ⟨rfl,by decide,?_⟩
  have he : EqE ((world swap).eval (.ternary .checkspk (wrap (.name 40)) (wrap cipher)
      (.spk (wrap (.name 40)) (.name 41) (wrap (.const .zero)) (wrap cipher)))) (.const .ok) :=
    (EqE.ternary .checkspk (RootStep.fst _ _).sound (RootStep.fst _ _).sound
      (.spk (RootStep.fst _ _).sound (.refl _) (RootStep.fst _ _).sound (RootStep.fst _ _).sound)).trans
      (RootStep.check_zero _ _).sound
  apply constructed_check_success_transfer (world swap) (world swap) _ _ _ _ _ _
    (by simp only [Term.Public]; decide)
    (by simp only [Term.Public]; decide)
    (by simp only [Term.Public]; decide) ?_ he
  intro r s _ _ _
  rfl

/-- The minimized binding defect changes only the fourth proof argument's
nonce. The supplied ciphertext and the proof's first three arguments agree. -/
theorem wrong_binding_rejected (swap : Bool) :
    ¬ EqE ((world swap).eval (.ternary .checkspk (.name 40) cipher
      (.spk (.name 40) (.name 41) (.const .zero)
        (.ternary .penc (.name 40) (.name 42) (.const .zero))))) (.const .ok) := by
  intro he
  obtain ⟨_,_,_,_,hp⟩ := (EqE.check_ok_iff_components _ _ _).mp he
  have h := (EqE.name_iff 42 41).mp
    ((EqE.penc_iff _ _ _ _ _ _).mp ((EqE.spk_iff _ _ _ _ _ _ _ _).mp hp).2.2.2).2.1
  omega

/-- Changing only the supplied key rejects an otherwise valid proof. -/
theorem wrong_key_rejected (swap : Bool) :
    ¬ EqE ((world swap).eval (.ternary .checkspk (.name 42) cipher proof)) (.const .ok) := by
  intro he
  obtain ⟨_,_,_,_,hp⟩ := (EqE.check_ok_iff_components _ _ _).mp he
  have h := (EqE.name_iff 40 42).mp ((EqE.spk_iff _ _ _ _ _ _ _ _).mp hp).1
  omega

/-- Two ones remain invalid even with a consistent key, nonce and binding.
The existing global minimum of this numeral rules out both one-node bits. -/
theorem two_ones_rejected (swap : Bool) :
    let m : Recipe 3 := .binary .add (.const .one) (.const .one)
    let c := Term.ternary .penc (.name 40) (.name 41) m
    ¬ EqE ((world swap).eval (.ternary .checkspk (.name 40) c
      (.spk (.name 40) (.name 41) m c))) (.const .ok) := by
  dsimp only
  intro he
  obtain ⟨_,bit,_,_,hp⟩ := (EqE.check_ok_iff_components _ _ _).mp he
  have hm := (PaddedMinimumSPOT.numeric_padded_minima swap).2.1.minimum
  have h := hm.least (.const bit) trivial ((EqE.spk_iff _ _ _ _ _ _ _ _).mp hp).2.2.1
  change 3 ≤ 1 at h
  omega

/-- Reducible candidate representations and abstention validate every honest
component and aggregate in both worlds, for either voter. -/
theorem honest_checks (swap : Bool) (i : Fin 2) (j : Fin 2) :
    EqE ((world swap).eval (.ternary .checkspk (.var 0)
      (combinationRecipe (.leaf (i,j))) ((Term.var i.succ).project (2+j.val)))) (.const .ok) ∧
    EqE ((world swap).eval (.ternary .checkspk (.var 0)
      (combinationRecipe (voterCombination (n := 1) i)) ((Term.var i.succ).project 4))) (.const .ok) :=
  ⟨honest_component_check_recipe_valid names swap left right i j,
   honest_aggregate_check_recipe_valid names swap left right i⟩

/-- With one candidate, distinct proof selectors alias and both checks
succeed. No minimum claim is made for the longer aggregate selector. -/
theorem one_candidate_alias (swap : Bool) :
    ((Term.var 1 : Recipe 3).project 1) ≠ (Term.var 1).project 2 ∧
    EqE ((ProofObservationSPOT.oneWorld swap).eval ((Term.var 1).project 1))
      ((ProofObservationSPOT.oneWorld swap).eval ((Term.var 1).project 2)) ∧
    EqE ((ProofObservationSPOT.oneWorld swap).eval (.ternary .checkspk (.var 0)
      (combinationRecipe (n := 0) (.leaf (0,0))) ((Term.var 1).project 2))) (.const .ok) := by
  exact ⟨(ProofObservationSPOT.one_candidate_fields_coincide swap).1,
    (ProofObservationSPOT.one_candidate_fields_coincide swap).2,
    honest_aggregate_check_recipe_valid ProofObservationSPOT.oneNames swap
      ProofObservationSPOT.oneLeft ProofObservationSPOT.oneRight 0⟩

/-- Five candidate selectors cost 24 nodes. Comparing this aggregate against
itself costs 48, exceeding the 38-node check. Minimum-origin raw E0 equality
in the general proof avoids assuming this oversized observation. -/
theorem aggregate_comparison_exceeds_bound :
    let a := combinationRecipe (voterCombination (n := 4) 0)
    let c := (Term.var 1 : Recipe 3).project 10
    a.nodeCount=24 ∧ (Term.ternary .checkspk (.var 0) a c).nodeCount=38 ∧
    a.nodeCount+a.nodeCount=48 ∧
    ¬ a.nodeCount+a.nodeCount < (Term.ternary .checkspk (.var 0) a c).nodeCount := by decide

/-- Minimum atomic children alone do not ensure cross-frame success. The
historical origin restrictions and observation premise carry real content. -/
theorem arbitrary_frame_success_does_not_transfer :
    Frame.MinimumChildren (MinimumDestructorSPOT.probeFrame true) MinimumDestructorSPOT.probe ∧
    EqE ((MinimumDestructorSPOT.probeFrame true).eval MinimumDestructorSPOT.probe) (.const .ok) ∧
    ¬ EqE ((MinimumDestructorSPOT.probeFrame false).eval MinimumDestructorSPOT.probe) (.const .ok) := by
  exact ⟨⟨.of_nodeCount_one trivial rfl,.of_nodeCount_one trivial rfl,.of_nodeCount_one trivial rfl⟩,
    MinimumDestructorSPOT.ok_probe_detects_new_match.2.1,
    MinimumDestructorSPOT.ok_probe_detects_new_match.1⟩

/-- The reduced criterion has an inhabited diagonal instance while preserving
distinct public observations; it does not prove the different-vote instance. -/
theorem decryption_criterion_diagonal :
    Frame.StaticEq (frame names false left left) (frame names true left left) ∧
    ¬ EqE ((frame names true left left).eval (.name 40)) ((frame names true left left).eval (.name 41)) := by
  have h : Frame.SuccessfulDecryptionTransport (frame names false left left) (frame names true left left) := by
    intro r hp _ _ _ _ _
    obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (frame names false left left).value) r hp
    exact ⟨m,hm,he,he⟩
  exact ⟨staticEq_of_successful_decryption_transport names HistoricalFrameSPOT.fixture_names_fresh left left h h,
    LocalRootSPOT.remaining_transport_diagonal.2⟩

end ExplainableCrypto.Helios.Symbolic.SuccessfulCheckSPOT
