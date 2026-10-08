import ExplainableCrypto.Helios.Symbolic.DestructorArithmeticTransport
import ExplainableCrypto.Helios.Symbolic.ConstructedCiphertextExperiments

namespace ExplainableCrypto.Helios.Symbolic.ConstructedCiphertextSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world := LocalRootSPOT.world
abbrev nestedCipher : Recipe 3 := .ternary .penc LocalRootSPOT.key (.name 40) LocalRootSPOT.proof
abbrev publicTree : CiphertextAssembly 1 := .mul CiphertextGroupingSPOT.first CiphertextGroupingSPOT.second
abbrev fused : Recipe 3 := .ternary .penc publicTree.keyRecipe CiphertextGroupingSPOT.nonce CiphertextGroupingSPOT.payload

/-- The selected wrapped key costs four nodes. The fused public ciphertext has
11 nodes, exceeding the old component-only budget 8 but fitting the original 12. -/
theorem selected_key_budget (swap : Bool) :
    publicTree.keyRecipe.nodeCount = 4 ∧ publicTree.group.budget = 8 ∧
    publicTree.recipe.nodeCount = 12 ∧ fused.nodeCount = 11 ∧
    publicTree.group.budget < fused.nodeCount ∧ fused.nodeCount ≤ publicTree.recipe.nodeCount ∧
    EqE ((world swap).eval publicTree.recipe) ((world swap).eval fused) := by
  have hk : publicTree.KeyAgreement names (world swap) ((world swap).eval publicTree.keyRecipe) :=
    ⟨.refl _,(RootStep.fst _ _).sound.symm⟩
  exact ⟨rfl,rfl,rfl,rfl,by decide,by decide,
    publicTree.grouped_value names swap left right _ hk⟩

/-- Non-atomic minimum key/proof children give an exact 16-node minimum
ciphertext, shared with every destination frame under the same policy. -/
theorem nested_ciphertext_minimum (swap : Bool) :
    MinimalRecipe names.restricted (world swap).value nestedCipher ∧ nestedCipher.nodeCount = 16 ∧
    ∀ ψ : Frame names.restricted 3, Frame.SharedMinimum (world swap) ψ nestedCipher := by
  have h := LocalRootSPOT.nested_constructor_minima swap
  have hn : MinimalRecipe names.restricted (world swap).value (.name 40) :=
    .of_nodeCount_one (by change 40 ∉ names.restricted; decide) rfl
  have hm := minimum_penc_of_children names swap left right _ _ _ h.2.1 hn h.2.2.1
  exact ⟨hm,rfl,fun _ => .of_minimal hm⟩

/-- Freshness is absent from this closure: colliding honest nonces
still permit a four-node minimum encryption with a public nonce. -/
theorem colliding_names_constructor_minimum (swap : Bool) :
    let ns := ProofObservationSPOT.colliding
    ¬ ns.Fresh ∧ MinimalRecipe ns.restricted (frame ns swap right right).value
      (.ternary .penc (.var 0) (.name 40) (.const .zero)) := by
  refine ⟨ProofObservationSPOT.freshness_required.2,?_⟩
  exact minimum_penc_of_children ProofObservationSPOT.colliding swap right right _ _ _
    (.of_nodeCount_one trivial rfl)
    (.of_nodeCount_one (by change 40 ∉ ProofObservationSPOT.colliding.restricted; decide) rfl)
    (.of_nodeCount_one trivial rfl)

/-- The shrunk omitted-child premise defect is a removable nonce wrapper;
the smaller public ciphertext has the same value. -/
theorem minimum_nonce_child_required (swap : Bool) :
    let a : Recipe 3 := .ternary .penc (.var 0)
      (.unary .fst (.binary .pair (.name 40) (.const .bottom))) (.const .zero)
    a.Public names.restricted ∧ ¬ MinimalRecipe names.restricted (world swap).value a := by
  have h40 : (Term.name (V := Fin 3) 40).Public names.restricted := by change 40 ∉ names.restricted; decide
  refine ⟨⟨trivial,⟨h40,trivial⟩,trivial⟩,?_⟩
  intro hm
  exact hm.no_smaller (s := .ternary .penc (.var 0) (.name 40) (.const .zero))
    ⟨trivial,h40,trivial⟩ (.ternary .penc (.refl _) (RootStep.fst _ _).sound (.refl _)) (by decide)

def publishedFrame : Frame names.restricted 1 :=
  ⟨fun _ => .ternary .penc (.name 40) (.name 41) (.name 42)⟩

/-- A one-handle frame directly publishing an arbitrary public encryption
refutes extension of constructor closure beyond the actual initial frame. -/
theorem published_ciphertext_breaks_closure :
    MinimalRecipe names.restricted publishedFrame.value (.name 40) ∧
    MinimalRecipe names.restricted publishedFrame.value (.name 41) ∧
    MinimalRecipe names.restricted publishedFrame.value (.name 42) ∧
    ¬ MinimalRecipe names.restricted publishedFrame.value (.ternary .penc (.name 40) (.name 41) (.name 42)) := by
  refine ⟨.of_nodeCount_one (by change 40 ∉ names.restricted; decide) rfl,
    .of_nodeCount_one (by change 41 ∉ names.restricted; decide) rfl,
    .of_nodeCount_one (by change 42 ∉ names.restricted; decide) rfl,?_⟩
  intro hm
  exact hm.no_smaller (s := .var 0) trivial (.refl _) (by decide)

/-- Directly naming a restricted nonce matches an honest group. Publicness of
the nonce recipe is essential for excluding that group. -/
theorem public_nonce_policy_required (swap : Bool) :
    let g : CiphertextGroup 1 := .honest (.leaf (0,0))
    EqE (g.nonce names (world swap)) ((world swap).eval (.name (names.nonce 0 0))) ∧
    ¬ (Term.name (V := Fin 3) (names.nonce 0 0)).Public names.nonceNames ∧
    ¬ ∃ r p, g = .constructed r p := by
  refine ⟨.refl _,?_,?_⟩
  · exact fun h => h (names.nonce_mem_nonceNames 0 0)
  · rintro ⟨r,p,h⟩
    cases h

/-- The reduced criterion is inhabited on diagonal assignments with
nonconstant public observations; different-vote premises remain unproved. -/
theorem destructor_arithmetic_transport_diagonal :
    Frame.StaticEq (frame names false left left) (frame names true left left) ∧
    ¬ EqE ((frame names true left left).eval (.name 40)) ((frame names true left left).eval (.name 41)) := by
  have h : Frame.DestructorArithmeticRootTransport (frame names false left left) (frame names true left left) := by
    intro r hp _ _ _
    obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (frame names false left left).value) r hp
    exact ⟨m,hm,he,he⟩
  exact ⟨staticEq_of_destructor_arithmetic_transport names HistoricalFrameSPOT.fixture_names_fresh left left h h,
    LocalRootSPOT.remaining_transport_diagonal.2⟩

end ExplainableCrypto.Helios.Symbolic.ConstructedCiphertextSPOT
