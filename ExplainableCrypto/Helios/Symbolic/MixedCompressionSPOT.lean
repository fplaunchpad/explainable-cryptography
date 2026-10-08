import ExplainableCrypto.Helios.Symbolic.DecryptCheckSingleMixedTransport
import ExplainableCrypto.Helios.Symbolic.MixedCompressionExperiments

namespace ExplainableCrypto.Helios.Symbolic.MixedCompressionSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world := LocalRootSPOT.world
abbrev honest : Combination (HonestIndex 1) := .leaf (0,0)
abbrev repeated : Combination (HonestIndex 1) := .mul (.leaf (0,1)) (.leaf (0,1))
abbrev nonce : Recipe 3 := .binary .compose (.name 40) (.name 41)
abbrev publicA : CiphertextAssembly 1 := .constructed (.var 0) (.name 40) (.const .zero)
abbrev publicB : CiphertextAssembly 1 := .constructed
  (.unary .fst (.binary .pair (.var 0) (.const .bottom))) (.name 41) (.const .one)
abbrev tree : CiphertextAssembly 1 := .mul (.mul publicA publicB) (.mul (.honest (0,1)) (.honest (0,1)))
abbrev grouped : Recipe 3 := mixedCombinationRecipe nonce (.binary .add (.const .zero) (.const .one)) repeated
abbrev shortest : Recipe 3 := mixedCombinationRecipe nonce (.const .one) repeated

private theorem public40 : (Term.name (V := Fin 3) 40).Public names.restricted := by change 40 ∉ names.restricted; decide
private theorem public41 : (Term.name (V := Fin 3) 41).Public names.restricted := by change 41 ∉ names.restricted; decide
private theorem coherent (swap : Bool) : tree.Coherent (world swap) :=
  ⟨⟨trivial,trivial,(RootStep.fst _ _).sound.symm⟩,⟨trivial,trivial,.refl _⟩,.refl _⟩

/-- Repeated higher-index selectors cost seven nodes. Mixed compression
saves four nodes here; numeric simplification yields a fourteen-node shared
global minimum for the original twenty-node recipe in both assignments. -/
theorem indexed_mixed_shared_minimum (swap : Bool) :
    tree.constructedCount=2 ∧ tree.recipe.nodeCount=20 ∧ grouped.nodeCount=16 ∧
    shortest.nodeCount=14 ∧ (combinationRecipe repeated).nodeCount=7 ∧
    MinimalRecipe names.restricted (world swap).value shortest ∧
    Frame.SharedMinimum (world swap) (world (!swap)) tree.recipe := by
  have hn := minimum_compose_of_children names swap left right names.restricted _ _
    (.of_nodeCount_one public40 rfl) (.of_nodeCount_one public41 rfl)
  have hm := minimum_mixed_of_minimum_nonce_atomic_payload names HistoricalFrameSPOT.fixture_names_fresh
    swap left right nonce (.const .one) hn trivial rfl repeated
  have he (s : Bool) : EqE ((world s).eval tree.recipe) ((world s).eval shortest) :=
    (tree.mixed_compression_value names s left right rfl (coherent s)).trans
      (.binary .mul (.ternary .penc (.refl _) (.refl _) (.equation .zero_one)) (.refl _))
  exact ⟨rfl,rfl,rfl,rfl,rfl,hm,⟨shortest,hm,he swap,he (!swap)⟩⟩

/-- One already grouped public constructor gives no strict saving and can
already be globally minimum. -/
theorem single_constructor_strictness_refuted (swap : Bool) :
    let t : CiphertextAssembly 1 := .mul publicA (.honest (0,0))
    t.constructedCount=1 ∧ t.recipe.nodeCount=7 ∧
    ¬ (mixedCombinationRecipe (.name 40) (.const .zero) honest).nodeCount<t.recipe.nodeCount ∧
    MinimalRecipe names.restricted (world swap).value t.recipe :=
  ⟨rfl,rfl,by decide,minimum_mixed_of_minimum_nonce_atomic_payload names HistoricalFrameSPOT.fixture_names_fresh
    swap left right (.name 40) (.const .zero) (.of_nodeCount_one public40 rfl) trivial rfl honest⟩

/-- Counting every honest selector as two nodes would erase two real nodes
from the repeated higher-index fixture. -/
theorem honest_index_cost_required :
    repeated.indices.card=2 ∧ (combinationRecipe repeated).nodeCount=7 ∧
    (combinationRecipe repeated).nodeCount ≠ 2*repeated.indices.card+(repeated.indices.card-1) := by decide

/-- Coherence alone does not identify a constructed-only key with the honest
public key. The nonconstructed premise of key binding is necessary. -/
theorem honest_contribution_required_for_key_binding (swap : Bool) :
    let t : CiphertextAssembly 1 := .constructed (.name 40) (.name 41) (.const .zero)
    t.Coherent (world swap) ∧ ¬ EqE (publicKey names) ((world swap).eval t.keyRecipe) := by
  refine ⟨trivial,?_⟩
  intro he
  obtain ⟨u,hu,_⟩ := he.pk_irreducible_shape (name_irreducible 40)
  cases hu

abbrev paddedPayload : Recipe 3 := .binary .add (.name 41) (.const .zero)
abbrev singlePadded : Recipe 3 := mixedCombinationRecipe (.name 40) paddedPayload honest
abbrev singleShort : Recipe 3 := mixedCombinationRecipe (.name 40) (.name 41) honest

private theorem payload_minimum (swap : Bool) :
    MinimalRecipe names.restricted (world swap).value paddedPayload := by
  apply minimum_add_of_exact_cost names swap left right names.restricted paddedPayload ⟨public41,trivial⟩
  · intro a ha
    have h : a = .name 41 := by simpa [paddedPayload,Term.addSyntaxSummary,AddSummary.combine,AddSummary.atom,AddSummary.number] using ha
    subst a
    exact .of_nodeCount_one public41 rfl
  · rfl

/-- The unresolved one-constructor case is inhabited with minimum immediate
children: a minimum payload's zero becomes redundant beside an honest numeric
message. The nine-node parent has a seven-node shared minimum. -/
theorem one_constructor_payload_problem (swap : Bool) :
    DecryptCheckSingleMixedCase 1 (world swap) singlePadded ∧
    Frame.MinimumChildren (world swap) singlePadded ∧
    ¬ MinimalRecipe names.restricted (world swap).value singlePadded ∧
    singlePadded.nodeCount=9 ∧ singleShort.nodeCount=7 ∧
    Frame.SharedMinimum (world swap) (world (!swap)) singlePadded := by
  have hn : (Term.name (V := Fin 3) 40).Public names.nonceNames := by change 40 ∉ names.nonceNames; decide
  have he (s : Bool) : EqE ((world s).eval singlePadded) ((world s).eval singleShort) := by
    apply (mixedCombination_equality_iff names HistoricalFrameSPOT.fixture_names_fresh s left right
      (.name 40) paddedPayload (.name 40) (.name 41) hn hn honest honest).mpr
    refine ⟨rfl,.refl _,?_⟩
    exact (EqE.equation (.assoc .add trivial _ _ _)).trans
      (.binary .add (.refl _) (.equation .zero_zero))
  have hm := minimum_mixed_of_minimum_nonce_atomic_payload names HistoricalFrameSPOT.fixture_names_fresh
    swap left right (.name 40) (.name 41) (.of_nodeCount_one public40 rfl) public41 rfl honest
  let t : CiphertextAssembly 1 := .mul (.constructed (.var 0) (.name 40) paddedPayload) (.honest (0,0))
  refine ⟨⟨t,rfl,⟨trivial,trivial,.refl _⟩,rfl,_,_,_,rfl⟩,
    ⟨minimum_penc_of_children names swap left right _ _ _ (.of_nodeCount_one trivial rfl)
      (.of_nodeCount_one public40 rfl) (payload_minimum swap),
      minimum_honest_combination names HistoricalFrameSPOT.fixture_names_fresh swap left right honest⟩,
    ?_,rfl,rfl,⟨singleShort,hm,he swap,he (!swap)⟩⟩
  intro h
  exact h.no_smaller hm.isPublic (he swap) (by decide)

/-- A removable nonce wrapper defeats minimum size even with an atomic
payload. The nonce-minimum premise is load-bearing. -/
theorem nonce_minimum_required (swap : Bool) :
    let r : Recipe 3 := mixedCombinationRecipe (MinimumTransportSPOT.reveal (.name 40)) (.const .zero) honest
    r.nodeCount=10 ∧ ¬ MinimalRecipe names.restricted (world swap).value r := by
  refine ⟨rfl,?_⟩
  intro hm
  have hp := mixedCombination_public (.name 40) (.const .zero) public40 trivial honest
  exact hm.no_smaller hp (.binary .mul
    (.ternary .penc (.refl _) (RootStep.fst _ _).sound (.refl _)) (.refl _)) (by decide)

/-- Every minimum competitor of the repeated-index fixture has exactly one
public constructor; its syntax may regroup the same honest occurrence bag. -/
theorem minimum_competitor_has_one_constructor (swap : Bool) (m : Recipe 3)
    (hm : MinimalRecipe names.restricted (world swap).value m)
    (he : EqE ((world swap).eval m) ((world swap).eval shortest)) :
    ∃ t : CiphertextAssembly 1, t.recipe=m ∧ t.constructedCount=1 := by
  obtain ⟨t,_,_,_,ht,_,hc,_⟩ := minimum_mixed_combination_origin names HistoricalFrameSPOT.fixture_names_fresh
    swap left right nonce (.const .one) ⟨by change 40 ∉ names.nonceNames; decide,by change 41 ∉ names.nonceNames; decide⟩
    trivial repeated m hm he
  exact ⟨t,ht,hc⟩

/-- The reduced criterion is inhabited on the identical-vote diagonal and
does not collapse distinct public observations. -/
theorem reduced_single_mixed_criterion_diagonal :
    Frame.StaticEq (frame names false left left) (frame names true left left) ∧
    ¬ EqE ((frame names true left left).eval (.name 40)) ((frame names true left left).eval (.name 41)) := by
  have h : DecryptCheckSingleMixedTransport 1 (frame names false left left) (frame names true left left) := by
    intro r hp _ _ _ _ _
    obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (frame names false left left).value) r hp
    exact ⟨m,hm,he,he⟩
  exact ⟨staticEq_of_decrypt_check_single_mixed_transport names HistoricalFrameSPOT.fixture_names_fresh left left h h,
    LocalRootSPOT.remaining_transport_diagonal.2⟩

end ExplainableCrypto.Helios.Symbolic.MixedCompressionSPOT
