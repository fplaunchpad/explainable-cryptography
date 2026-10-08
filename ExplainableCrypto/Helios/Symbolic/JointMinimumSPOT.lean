import ExplainableCrypto.Helios.Symbolic.DecryptCheckMixedMulTransport
import ExplainableCrypto.Helios.Symbolic.JointMinimumExperiments

namespace ExplainableCrypto.Helios.Symbolic.JointMinimumSPOT
open Historical General JointMinimumExperiments
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world := LocalRootSPOT.world

/-- In this independent finite inference model every source recipe is minimum.
A destination merge makes one recipe nonminimum and hides it from the step. -/
theorem reverse_minima_required :
    below costs distinct merged 4 = true ∧ bothStep costs distinct merged = true ∧
    below costs merged distinct 4 = false ∧ observations costs distinct merged 4 = false := by decide

/-- With equal costs, both shared-minimum hypotheses hold even though the
destination merges values. The minimum observation step excludes this model. -/
theorem minimum_step_required :
    let size : Fin 4 → Nat := fun _ => 1
    below size distinct merged 3 = true ∧ below size merged distinct 3 = true ∧
    bothStep size distinct merged = false ∧ observations size distinct merged 3 = false := by decide

/-- Two-way minima below two do not justify a size-three observation. The
bounded theorem preserves the supplied bound exactly. -/
theorem same_bound_required :
    positive costs distinct merged 2 = true ∧ observations costs distinct merged 2 = true ∧
    observations costs distinct merged 4 = false := by decide

private theorem small_minima (swap swap' : Bool) :
    Frame.SharedMinimaBelow (world swap) (world swap') 3 := by
  intro r hp hsize
  rcases r.nodeCount_two_cases (by omega) with ha | ⟨f,a,rfl,ha⟩
  · exact .of_minimal (.of_nodeCount_one hp (Nat.le_antisymm ha r.nodeCount_pos))
  · have hm : MinimalRecipe names.restricted (world swap).value a :=
      .of_nodeCount_one hp (Nat.le_antisymm ha a.nodeCount_pos)
    cases f with
    | pk => exact .of_minimal (minimum_pk_of_child names swap left right a hm)
    | fst =>
      exact minimum_child_projection_shared names HistoricalFrameSPOT.fixture_names_fresh
        swap swap' left right .fst (Or.inl rfl) a hm
    | snd =>
      exact minimum_child_projection_shared names HistoricalFrameSPOT.fixture_names_fresh
        swap swap' left right .snd (Or.inr rfl) a hm

/-- Actual different-vote frames inhabit two-way bounded minima. Their
size-two equality tests transfer and still distinguish distinct public names. -/
theorem bounded_initial_observations (swap : Bool) :
    Frame.SharedMinimaBelow (world swap) (world (!swap)) 3 ∧
    Frame.SharedMinimaBelow (world (!swap)) (world swap) 3 ∧
    Frame.ObservationsBelow (world swap) (world (!swap)) 3 ∧
    ¬ EqE ((world (!swap)).eval (.name 40)) ((world (!swap)).eval (.name 41)) := by
  refine ⟨small_minima swap (!swap),small_minima (!swap) swap,
    observationsBelow_of_two_way_minima names HistoricalFrameSPOT.fixture_names_fresh
      swap (!swap) left right 3 (small_minima swap (!swap)) (small_minima (!swap) swap),?_⟩
  intro he
  have h := (EqE.name_iff 40 41).mp he
  omega

/-- The new induction never asserts that a child/minimum comparison fits
the parent's observation budget; the previous nine-versus-eight control remains. -/
theorem child_comparison_still_exceeds_budget :
    MinimumTransportSPOT.child.nodeCount + MinimumTransportSPOT.minimumPair.nodeCount = 9 ∧
    MinimumTransportSPOT.parent.nodeCount + (Term.name (V := Fin 0) 40).nodeCount = 8 := by decide

abbrev publicA : CiphertextAssembly 1 := .constructed (.var 0) (.name 40) (.const .zero)
abbrev publicB : CiphertextAssembly 1 := .constructed (.var 0) (.name 41) (.const .one)
abbrev mixed : CiphertextAssembly 1 := .mul (.mul publicA publicB) (.honest (0,0))
abbrev shortened : Recipe 3 := .binary .mul
  (.ternary .penc (.var 0) (.binary .compose (.name 40) (.name 41)) (.const .one))
  ((Term.var (1 : Fin 3)).project 0)

/-- A public coherent mixed product is a real nonminimum case: twelve raw
nodes have a nine-node equivalent. Minimum immediate children are not asserted
for this control; that remains a premise of the local transport interface. -/
theorem mixed_case_not_omitted (swap : Bool) :
    DecryptCheckMixedMulCase 1 (world swap) mixed.recipe ∧
    mixed.recipe.Public names.restricted ∧ mixed.recipe.nodeCount = 12 ∧
    shortened.nodeCount = 9 ∧ ¬ MinimalRecipe names.restricted (world swap).value mixed.recipe := by
  have hp40 : (Term.name (V := Fin 3) 40).Public names.restricted := by change 40 ∉ names.restricted; decide
  have hp41 : (Term.name (V := Fin 3) 41).Public names.restricted := by change 41 ∉ names.restricted; decide
  have he : EqE mixed.recipe shortened := .binary .mul
    ((RootStep.homomorphic _ _ _ _ _).sound.trans
      (.ternary .penc (.refl _) (.refl _) (.equation .zero_one))) (.refl _)
  refine ⟨⟨mixed,rfl,⟨⟨trivial,trivial,.refl _⟩,trivial,.refl _⟩,_,_,_,rfl⟩,
    ⟨⟨⟨trivial,hp40,trivial⟩,⟨trivial,hp41,trivial⟩⟩,trivial⟩,rfl,rfl,?_⟩
  intro hm
  exact hm.no_smaller (s := shortened) ⟨⟨trivial,⟨hp40,hp41⟩,trivial⟩,trivial⟩
    (he.subst _) (by decide)

/-- The reduced criterion and simultaneous induction are inhabited. This
diagonal control preserves nonconstant observations and does not prove secrecy
for different votes; the general remaining premises stay explicit. -/
theorem reduced_joint_criterion_diagonal :
    Frame.StaticEq (frame names false left left) (frame names true left left) ∧
    ¬ EqE ((frame names true left left).eval (.name 40)) ((frame names true left left).eval (.name 41)) := by
  have h : DecryptCheckMixedMulTransport 1 (frame names false left left) (frame names true left left) := by
    intro r hp _ _ _ _ _
    obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (frame names false left left).value) r hp
    exact ⟨m,hm,he,he⟩
  exact ⟨staticEq_of_decrypt_check_mixed_mul_transport names HistoricalFrameSPOT.fixture_names_fresh
    left left h h,LocalRootSPOT.remaining_transport_diagonal.2⟩

/-- The generic simultaneous theorem applies to every recipe, including a
strictly reducible wrapper. Its result is not restricted to minimum parents. -/
theorem joint_lifting_reducible_wrapper :
    Frame.CommonMinima MinimumTransportSPOT.source MinimumTransportSPOT.source ∧
    ¬ MinimalRecipe ∅ MinimumTransportSPOT.source.value
      (MinimumTransportSPOT.reveal (.name 40)) := by
  have h : Frame.JointLocalMinimumTransport MinimumTransportSPOT.source MinimumTransportSPOT.source := by
    intro r hp _ _ _
    obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := MinimumTransportSPOT.source.value) r hp
    exact ⟨m,hm,he,he⟩
  exact ⟨(Frame.common_minima_of_joint_local h h).1,MinimumTransportSPOT.raw_wrapper_shared.2.2⟩

end ExplainableCrypto.Helios.Symbolic.JointMinimumSPOT
