import ExplainableCrypto.Helios.Symbolic.DecryptCheckMulTransport
import ExplainableCrypto.Helios.Symbolic.AdditionMinimumExperiments

namespace ExplainableCrypto.Helios.Symbolic.AdditionMinimumSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world := LocalRootSPOT.world

/-- The two numeric equations yield one-node minima, but their three-node
parents are not minimum even with minimum children. -/
theorem numeric_collapses (swap : Bool) :
    Frame.SharedMinimum (world swap) (world (!swap)) (.binary .add (.const .zero) (.const .zero)) ∧
    Frame.SharedMinimum (world swap) (world (!swap)) (.binary .add (.const .zero) (.const .one)) ∧
    ¬ MinimalRecipe names.restricted (world swap).value (.binary .add (.const .zero) (.const .zero)) := by
  have hz : MinimalRecipe names.restricted (world swap).value (.const .zero) := .of_nodeCount_one trivial rfl
  have ho : MinimalRecipe names.restricted (world swap).value (.const .one) := .of_nodeCount_one trivial rfl
  refine ⟨minimum_children_add_shared names swap left right _ _ hz hz _,
    minimum_children_add_shared names swap left right _ _ hz ho _,?_⟩
  intro hm
  exact hm.no_smaller (s := .const .zero) trivial (EqE.equation .zero_zero) (by decide)

/-- Separated zeros can be removed from a positive numeric contribution,
but the two remaining ones are a three-node minimum, not a saturated one. -/
theorem separated_numeric_minimum (swap : Bool) :
    let r : Recipe 3 := .binary .add (.binary .add (.const .zero) (.const .one))
      (.binary .add (.const .one) (.const .zero))
    let s : Recipe 3 := .binary .add (.const .one) (.const .one)
    BaseEq r s ∧ MinimalRecipe names.restricted (world swap).value s ∧
    r.nodeCount = 7 ∧ s.nodeCount = 3 ∧
    ¬ EqE (Term.binary (V := Empty) .add (.const .one) (.const .one)) (.const .one) := by
  refine ⟨baseEq_of_addSyntaxSummary_eq (by rfl),?_,rfl,rfl,AdditionObservationSPOT.numeric_count_is_observable⟩
  exact minimum_add_of_exact_cost names swap left right names.restricted _ ⟨trivial,trivial⟩
    (by intro a ha; simp [Term.addSyntaxSummary,AddSummary.combine,AddSummary.number] at ha) rfl

/-- A present zero and a duplicate name both remain in globally minimum
three-node additions; neither is an unobservable unit or idempotent occurrence. -/
theorem zero_and_duplicate_atoms (swap : Bool) :
    MinimalRecipe names.restricted (world swap).value (.binary .add (.name 40) (.const .zero)) ∧
    MinimalRecipe names.restricted (world swap).value (.binary .add (.name 40) (.name 40)) ∧
    ¬ EqE (Term.binary (V := Empty) .add (.name 40) (.const .zero)) (.name 40) ∧
    ¬ EqE (Term.binary (V := Empty) .add (.name 40) (.name 40)) (.name 40) := by
  have hp : (Term.name (V := Fin 3) 40).Public names.restricted := by change 40 ∉ names.restricted; decide
  have hm : MinimalRecipe names.restricted (world swap).value (.name 40) := .of_nodeCount_one hp rfl
  refine ⟨minimum_add_of_exact_cost names swap left right names.restricted _ ⟨hp,trivial⟩ ?_ rfl,
    minimum_add_of_exact_cost names swap left right names.restricted _ ⟨hp,hp⟩ ?_ rfl,
    AdditionObservationSPOT.numeric_presence_is_observable.2.2,AdditionObservationSPOT.duplicates_are_observable⟩
  all_goals
    intro a ha
    simp [Term.addSyntaxSummary,AddSummary.combine,AddSummary.atom,AddSummary.number] at ha
    subst a
    exact hm

abbrev redundant : Recipe 3 := .binary .add
  (.binary .add LocalRootSPOT.key (.const .zero)) (.binary .add LocalRootSPOT.key (.const .one))
abbrev shortest : Recipe 3 := .binary .add (.binary .add LocalRootSPOT.key LocalRootSPOT.key) (.const .one)

/-- Repeated four-node atoms survive; only redundant numeric syntax is
removed. The eleven-node result is minimum and shared in every destination. -/
theorem non_atomic_shared_minimum (swap : Bool) (ψ : Frame names.restricted 3) :
    BaseEq redundant shortest ∧ MinimalRecipe names.restricted (world swap).value shortest ∧
    redundant.nodeCount = 13 ∧ shortest.nodeCount = 11 ∧
    ¬ MinimalRecipe names.restricted (world swap).value redundant ∧
    Frame.SharedMinimum (world swap) ψ redundant := by
  have hk := (LocalRootSPOT.nested_constructor_minima swap).2.1
  have he : BaseEq redundant shortest := baseEq_of_addSyntaxSummary_eq (by
    simp [Term.addSyntaxSummary,AddSummary.combine,AddSummary.atom,AddSummary.number,numericAdd])
  have hm := minimum_add_of_exact_cost names swap left right names.restricted shortest
    ⟨⟨hk.isPublic,hk.isPublic⟩,trivial⟩ (by
      intro a ha
      simp [Term.addSyntaxSummary,AddSummary.combine,AddSummary.atom,AddSummary.number] at ha
      subst a
      exact hk) rfl
  refine ⟨he,hm,rfl,rfl,?_,.of_recipe_eqE hm he.sound⟩
  intro hr
  exact hr.no_smaller hm.isPublic (he.sound.subst _) (by decide)

/-- A nonminimum raw atom invalidates cost-attainment as a proof of global
minimality: the projection wrapper can be removed. -/
theorem minimum_atom_required (swap : Bool) :
    let r : Recipe 3 := .binary .add
      (.unary .fst (.binary .pair (.name 40) (.const .bottom))) (.name 41)
    r.nodeCount+1 = r.addSyntaxSummary.recipeCost ∧
    r.Public names.restricted ∧ ¬ MinimalRecipe names.restricted (world swap).value r := by
  have h40 : (Term.name (V := Fin 3) 40).Public names.restricted := by change 40 ∉ names.restricted; decide
  have h41 : (Term.name (V := Fin 3) 41).Public names.restricted := by change 41 ∉ names.restricted; decide
  refine ⟨rfl,⟨⟨h40,trivial⟩,h41⟩,?_⟩
  intro hm
  exact hm.no_smaller (s := .binary .add (.name 40) (.name 41)) ⟨h40,h41⟩
    (.binary .add (RootStep.fst _ _).sound (.refl _)) (by decide)

/-- The source cost result also works with a weaker caller policy and
colliding nonces. This particular recipe is not public under the full policy. -/
theorem weaker_policy_and_colliding_names (swap : Bool) :
    let ns := ProofObservationSPOT.colliding
    let r : Recipe 3 := .binary .add (.name ns.secretKey) (.name 40)
    ¬ ns.Fresh ∧ MinimalRecipe ns.nonceNames (frame ns swap right right).value r ∧
    ¬ r.Public ns.restricted := by
  have hk : (Term.name (V := Fin 3) ProofObservationSPOT.colliding.secretKey).Public
      ProofObservationSPOT.colliding.nonceNames := by
    change ProofObservationSPOT.colliding.secretKey ∉ ProofObservationSPOT.colliding.nonceNames
    decide
  have h40 : (Term.name (V := Fin 3) 40).Public ProofObservationSPOT.colliding.nonceNames := by
    change 40 ∉ ProofObservationSPOT.colliding.nonceNames
    decide
  refine ⟨ProofObservationSPOT.freshness_required.2,?_,?_⟩
  · apply minimum_add_of_exact_cost ProofObservationSPOT.colliding swap right right
      ProofObservationSPOT.colliding.nonceNames
      (.binary .add (.name ProofObservationSPOT.colliding.secretKey) (.name 40)) ⟨hk,h40⟩ ?_ rfl
    intro a ha
    simp [Term.addSyntaxSummary,AddSummary.combine,AddSummary.atom] at ha
    rcases ha with rfl | rfl
    · exact .of_nodeCount_one hk rfl
    · exact .of_nodeCount_one h40 rfl
  · intro h
    exact h.1 (by decide)

def publishedFrame : Frame names.restricted 1 := ⟨fun _ => .binary .add (.name 40) (.name 41)⟩

/-- A public handle for a sum breaks the initial-frame cost theorem even
when its literal atoms are minimum and its raw cost is attained. -/
theorem initial_frame_required :
    MinimalRecipe names.restricted publishedFrame.value (.name 40) ∧
    MinimalRecipe names.restricted publishedFrame.value (.name 41) ∧
    ¬ MinimalRecipe names.restricted publishedFrame.value (.binary .add (.name 40) (.name 41)) := by
  refine ⟨.of_nodeCount_one (by change 40 ∉ names.restricted; decide) rfl,
    .of_nodeCount_one (by change 41 ∉ names.restricted; decide) rfl,?_⟩
  intro hm
  exact hm.no_smaller (s := .var 0) trivial (.refl _) (by decide)

/-- The reduced criterion is inhabited for identical votes and preserves
distinct public observations. This is not a different-vote secrecy theorem. -/
theorem three_case_transport_diagonal :
    Frame.StaticEq (frame names false left left) (frame names true left left) ∧
    ¬ EqE ((frame names true left left).eval (.name 40)) ((frame names true left left).eval (.name 41)) := by
  have h : Frame.DecryptCheckMulTransport (frame names false left left) (frame names true left left) := by
    intro r hp _ _ _
    obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (frame names false left left).value) r hp
    exact ⟨m,hm,he,he⟩
  exact ⟨staticEq_of_decrypt_check_mul_transport names HistoricalFrameSPOT.fixture_names_fresh left left h h,
    LocalRootSPOT.remaining_transport_diagonal.2⟩

end ExplainableCrypto.Helios.Symbolic.AdditionMinimumSPOT
