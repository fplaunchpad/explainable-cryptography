import ExplainableCrypto.Helios.Symbolic.DecryptCheckAddMulTransport
import ExplainableCrypto.Helios.Symbolic.CompositionMinimumExperiments

namespace ExplainableCrypto.Helios.Symbolic.CompositionMinimumSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world := LocalRootSPOT.world
abbrev first : Recipe 3 := .binary .compose LocalRootSPOT.key (.binary .compose (.var 1) LocalRootSPOT.key)
abbrev second : Recipe 3 := .binary .compose (.binary .compose LocalRootSPOT.key LocalRootSPOT.key) (.var 1)

/-- Repeated four-node minimum leaves retain their costs under reassociation
and permutation. Both different eleven-node recipes are minimum. -/
theorem non_atomic_reassociation (swap : Bool) :
    MinimalRecipe names.restricted (world swap).value first ∧
    MinimalRecipe names.restricted (world swap).value second ∧
    first ≠ second ∧ EqE first second ∧ first.nodeCount = 11 ∧
    first.composeLeaves.card = 3 ∧ (first.composeLeaves.map Term.nodeCount).sum = 9 ∧
    Frame.SharedMinimum (world swap) (world (!swap)) first := by
  have hk := (LocalRootSPOT.nested_constructor_minima swap).2.1
  have hv : MinimalRecipe names.restricted (world swap).value (.var 1) := .of_nodeCount_one trivial rfl
  have hfirst := minimum_compose_of_children names swap left right names.restricted _ _ hk
    (minimum_compose_of_children names swap left right names.restricted _ _ hv hk)
  have hsecond := minimum_compose_of_children names swap left right names.restricted _ _
    (minimum_compose_of_children names swap left right names.restricted _ _ hk hk) hv
  have he : EqE first second := eqE_of_compose_value_factors (by
    simp only [Term.composeValueFactors]
    ac_rfl)
  exact ⟨hfirst,hsecond,by decide,he,rfl,rfl,rfl,.of_minimal hfirst⟩

/-- Neither zero nor a repeated occurrence disappears from composition, and
both literal compositions attain the three-node minimum in actual frames. -/
theorem zero_and_duplicates_remain (swap : Bool) :
    MinimalRecipe names.restricted (world swap).value (.binary .compose (.const .zero) (.name 40)) ∧
    MinimalRecipe names.restricted (world swap).value (.binary .compose (.name 40) (.name 40)) ∧
    ¬ EqE (Term.binary (V := Empty) .compose (.const .zero) (.name 40)) (.name 40) ∧
    ¬ EqE (Term.binary (V := Empty) .compose (.name 40) (.name 40)) (.name 40) := by
  have hn : MinimalRecipe names.restricted (world swap).value (.name 40) :=
    .of_nodeCount_one (by change 40 ∉ names.restricted; decide) rfl
  exact ⟨minimum_compose_of_children names swap left right names.restricted _ _ (.of_nodeCount_one trivial rfl) hn,
    minimum_compose_of_children names swap left right names.restricted _ _ hn hn,
    CompositionObservationSPOT.composition_has_no_zero_unit.2,
    CompositionObservationSPOT.duplicates_are_observable⟩

/-- The arbitrary caller policy may expose the secret key, and names may
collide. The same recipe is not public under the full name restriction. -/
theorem weaker_policy_and_colliding_names (swap : Bool) :
    let ns := ProofObservationSPOT.colliding
    let r : Recipe 3 := .binary .compose (.name ns.secretKey) (.name 40)
    ¬ ns.Fresh ∧ MinimalRecipe ns.nonceNames (frame ns swap right right).value r ∧
    ¬ r.Public ns.restricted := by
  refine ⟨ProofObservationSPOT.freshness_required.2,?_,?_⟩
  · exact minimum_compose_of_children ProofObservationSPOT.colliding swap right right
      ProofObservationSPOT.colliding.nonceNames _ _
      (.of_nodeCount_one (by change ProofObservationSPOT.colliding.secretKey ∉ ProofObservationSPOT.colliding.nonceNames; decide) rfl)
      (.of_nodeCount_one (by change 40 ∉ ProofObservationSPOT.colliding.nonceNames; decide) rfl)
  · intro h
    exact h.1 (by decide)

/-- A removable wrapper in a leaf permits a smaller public composition, so
minimum leaf size is essential to total-size closure. -/
theorem minimum_leaf_required (swap : Bool) :
    let r : Recipe 3 := .binary .compose
      (.unary .fst (.binary .pair (.name 40) (.const .bottom))) (.name 41)
    r.Public names.restricted ∧ ¬ MinimalRecipe names.restricted (world swap).value r := by
  have h40 : (Term.name (V := Fin 3) 40).Public names.restricted := by change 40 ∉ names.restricted; decide
  have h41 : (Term.name (V := Fin 3) 41).Public names.restricted := by change 41 ∉ names.restricted; decide
  refine ⟨⟨⟨h40,trivial⟩,h41⟩,?_⟩
  intro hm
  exact hm.no_smaller (s := .binary .compose (.name 40) (.name 41)) ⟨h40,h41⟩
    (.binary .compose (RootStep.fst _ _).sound (.refl _)) (by decide)

def publishedFrame : Frame names.restricted 1 :=
  ⟨fun _ => .binary .compose (.name 40) (.name 41)⟩

/-- Directly publishing a composed value creates a shorter handle even though
both literal children are minimum. This is outside the initial-frame theorem. -/
theorem published_composition_breaks_closure :
    MinimalRecipe names.restricted publishedFrame.value (.name 40) ∧
    MinimalRecipe names.restricted publishedFrame.value (.name 41) ∧
    ¬ MinimalRecipe names.restricted publishedFrame.value (.binary .compose (.name 40) (.name 41)) := by
  refine ⟨.of_nodeCount_one (by change 40 ∉ names.restricted; decide) rfl,
    .of_nodeCount_one (by change 41 ∉ names.restricted; decide) rfl,?_⟩
  intro hm
  exact hm.no_smaller (s := .var 0) trivial (.refl _) (by decide)

/-- Addition is still a real nonminimum case: its two zero children are
minimum, while the equation supplies a smaller shared zero representative. -/
theorem addition_still_requires_transport (swap : Bool) :
    let r : Recipe 3 := .binary .add (.const .zero) (.const .zero)
    Frame.DecryptCheckAddMulCase (world swap) r ∧ Frame.MinimumChildren (world swap) r ∧
    ¬ MinimalRecipe names.restricted (world swap).value r ∧
    Frame.SharedMinimum (world swap) (world (!swap)) r := by
  have h := LocalRootSPOT.remaining_numeric_case swap (world (!swap))
  exact ⟨trivial,h.1,h.2.2.1,h.2.2.2⟩

/-- The four-case criterion is inhabited on diagonal votes and retains
distinct public names. Different-vote premises remain unproved. -/
theorem four_case_transport_diagonal :
    Frame.StaticEq (frame names false left left) (frame names true left left) ∧
    ¬ EqE ((frame names true left left).eval (.name 40)) ((frame names true left left).eval (.name 41)) := by
  have h : Frame.DecryptCheckAddMulTransport (frame names false left left) (frame names true left left) := by
    intro r hp _ _ _
    obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (frame names false left left).value) r hp
    exact ⟨m,hm,he,he⟩
  exact ⟨staticEq_of_decrypt_check_add_mul_transport names HistoricalFrameSPOT.fixture_names_fresh left left h h,
    LocalRootSPOT.remaining_transport_diagonal.2⟩

end ExplainableCrypto.Helios.Symbolic.CompositionMinimumSPOT
