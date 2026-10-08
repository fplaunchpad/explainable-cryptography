import ExplainableCrypto.Helios.Symbolic.DecryptCheckTransport
import ExplainableCrypto.Helios.Symbolic.PaddedMinimumExperiments

namespace ExplainableCrypto.Helios.Symbolic.PaddedMinimumSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world := LocalRootSPOT.world
abbrev key := LocalRootSPOT.key
abbrev duplicate : Recipe 3 := .binary .add key key
abbrev padded : Recipe 3 := .binary .add duplicate (.const .zero)
abbrev nonce : Recipe 3 := .binary .compose (.name 40) (.name 41)
abbrev honest := MixedCompressionSPOT.repeated

private theorem public40 : (Term.name (V := Fin 3) 40).Public names.restricted := by change 40 ∉ names.restricted; decide
private theorem public41 : (Term.name (V := Fin 3) 41).Public names.restricted := by change 41 ∉ names.restricted; decide
private theorem duplicate_minimum (swap : Bool) : PaddedMinimalRecipe names.restricted (world swap).value duplicate := by
  have hk := (LocalRootSPOT.nested_constructor_minima swap).2.1
  apply padded_minimum_of_exact_cost names swap left right names.restricted duplicate ⟨hk.isPublic,hk.isPublic⟩
  · intro a ha
    have h : a=key := by simpa [duplicate,key,LocalRootSPOT.key,Term.addSyntaxSummary,AddSummary.combine,AddSummary.atom] using ha
    subst a
    exact hk
  · rfl

/-- Two four-node atoms retain both occurrences. Removing a redundant zero
gives a nine-node global padded minimum from eleven nodes. -/
theorem duplicate_atoms_padded_minimum (swap : Bool) :
    PaddedMinimalRecipe names.restricted (world swap).value duplicate ∧
    duplicate.nodeCount=9 ∧ padded.nodeCount=11 ∧
    duplicate.addSyntaxSummary.paddedRecipeCost=10 ∧
    BaseEq (.binary .add padded (.const .zero)) (.binary .add duplicate (.const .zero)) ∧
    ¬ EqE ((world swap).eval (.binary .add duplicate (.const .zero)))
      ((world swap).eval (.binary .add key (.const .zero))) := by
  have hm := duplicate_minimum swap
  refine ⟨hm,rfl,rfl,rfl,?_,?_⟩
  · exact (BaseEq.equation (.assoc .add trivial _ _ _)).trans (.binary .add (.refl _) (.equation .zero_zero))
  · intro he
    have h := hm.2 key (LocalRootSPOT.nested_constructor_minima swap).2.1.isPublic he
    change 9 ≤ 4 at h
    omega

/-- All-zero payloads still need one node, and two ones still need three.
Zero padding does not erase a one or introduce an empty recipe. -/
theorem numeric_padded_minima (swap : Bool) :
    PaddedMinimalRecipe names.restricted (world swap).value (.const .zero) ∧
    PaddedMinimalRecipe names.restricted (world swap).value (.binary .add (.const .one) (.const .one)) ∧
    ¬ EqE ((world swap).eval (.binary .add (.binary .add (.const .one) (.const .one)) (.const .zero)))
      ((world swap).eval (.binary .add (.const .one) (.const .zero))) := by
  have hz : PaddedMinimalRecipe names.restricted (world swap).value (.const .zero) :=
    ⟨trivial,fun s _ _ => s.nodeCount_pos⟩
  have ho : PaddedMinimalRecipe names.restricted (world swap).value (.binary .add (.const .one) (.const .one)) := by
    apply padded_minimum_of_exact_cost names swap left right names.restricted
      (.binary .add (.const .one) (.const .one)) ⟨trivial,trivial⟩
    · intro a ha
      simp [Term.addSyntaxSummary,AddSummary.combine,AddSummary.number] at ha
    · rfl
  refine ⟨hz,ho,?_⟩
  intro he
  have h := ho.2 (.const .one) trivial he
  change 3 ≤ 1 at h
  omega

/-- Zero cancellation is justified only by the padded relation; it is not
an equation between a public atom and that atom plus zero. -/
theorem unpadded_zero_cancellation_refuted (swap : Bool) :
    ¬ EqE ((world swap).eval (.binary .add (.name 40) (.const .zero))) ((world swap).eval (.name 40)) := by
  intro he
  have hb := (irreducible_eqE_iff_base ((name_irreducible 40).add (constant_irreducible .zero))
    (name_irreducible 40)).mp he
  have hs := (baseEq_iff_addSummary _ _).mp hb
  have hn := congrArg AddSummary.numeric hs
  cases hn

/-- A wrapped atom attains the raw skeleton cost but is not a padded minimum.
The semantic minimum-atom premise excludes this counterexample. -/
theorem minimum_atoms_required (swap : Bool) :
    let r : Recipe 3 := MinimumTransportSPOT.reveal (.name 40)
    r.nodeCount+1=r.addSyntaxSummary.paddedRecipeCost ∧
    ¬ PaddedMinimalRecipe names.restricted (world swap).value r := by
  refine ⟨rfl,?_⟩
  intro hm
  have h := hm.2 (.name 40) public40 (.binary .add (RootStep.fst _ _).sound (.refl _))
  change 4 ≤ 1 at h
  omega

/-- The mixed theorem now handles a genuinely non-atomic padded payload:
three nonce nodes, nine payload nodes and seven honest-selector nodes give
a twenty-two-node shared minimum from a twenty-four-node mixed recipe. -/
theorem non_atomic_mixed_minimum (swap : Bool) :
    let r := mixedCombinationRecipe nonce padded honest
    let s := mixedCombinationRecipe nonce duplicate honest
    MinimalRecipe names.restricted (world swap).value s ∧ r.nodeCount=24 ∧ s.nodeCount=22 ∧
    Frame.SharedMinimum (world swap) (world (!swap)) r := by
  have hn := minimum_compose_of_children names swap left right names.restricted _ _
    (.of_nodeCount_one public40 rfl) (.of_nodeCount_one public41 rfl)
  have hm := minimum_mixed_of_minimum_components names HistoricalFrameSPOT.fixture_names_fresh swap left right
    nonce duplicate hn (duplicate_minimum swap) honest
  have hp : nonce.Public names.nonceNames := ⟨by change 40 ∉ names.nonceNames; decide,by change 41 ∉ names.nonceNames; decide⟩
  have he (s : Bool) : EqE ((world s).eval (mixedCombinationRecipe nonce padded honest))
      ((world s).eval (mixedCombinationRecipe nonce duplicate honest)) :=
    (mixedCombination_equality_iff names HistoricalFrameSPOT.fixture_names_fresh s left right
      nonce padded nonce duplicate hp hp honest honest).mpr
      ⟨rfl,.refl _,(duplicate_atoms_padded_minimum s).2.2.2.2.1.sound.subst _⟩
  exact ⟨hm,rfl,rfl,⟨_,hm,he swap,he (!swap)⟩⟩

/-- The sole constructor's components are not minimum when a raw
multiplication leaf contains a removable nonce wrapper. -/
theorem minimum_leaves_required (swap : Bool) :
    let t : CiphertextAssembly 1 := .mul
      (.constructed (.var 0) (MinimumTransportSPOT.reveal (.name 40)) (.const .zero)) (.honest (0,0))
    t.constructedCount=1 ∧ t.Coherent (world swap) ∧
    ¬ MinimalRecipe names.restricted (world swap).value (MinimumTransportSPOT.reveal (.name 40)) := by
  refine ⟨rfl,⟨trivial,trivial,.refl _⟩,?_⟩
  intro hm
  exact hm.no_smaller public40 (RootStep.fst _ _).sound (by decide)

/-- The full multiplication operator theorem applies to the previously open
minimum-child zero-padding fixture; multiplication is absent from the new case. -/
theorem multiplication_discharged (swap : Bool) :
    Frame.SharedMinimum (world swap) (world swap) MixedCompressionSPOT.singlePadded ∧
    ¬ Frame.DecryptCheckCase (world swap) MixedCompressionSPOT.singlePadded := by
  have hc := (MixedCompressionSPOT.one_constructor_payload_problem swap).2.1
  have hs : Frame.SharedMinimaBelow (world swap) (world swap) MixedCompressionSPOT.singlePadded.nodeCount := by
    intro r hp _
    obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (world swap).value) r hp
    exact ⟨m,hm,he,he⟩
  exact ⟨minimum_children_mul_shared_of_two_way_minima names HistoricalFrameSPOT.fixture_names_fresh
    swap swap left right _ _ hc.1 hc.2 hs hs,not_false⟩

/-- Successful destructors remain explicit in the reduced criterion, whose
diagonal instance is inhabited and retains distinct public-name observations. -/
theorem decrypt_check_criterion_diagonal :
    Frame.StaticEq (frame names false left left) (frame names true left left) ∧
    ¬ EqE ((frame names true left left).eval (.name 40)) ((frame names true left left).eval (.name 41)) := by
  have h : Frame.DecryptCheckTransport (frame names false left left) (frame names true left left) := by
    intro r hp _ _ _ _ _
    obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (frame names false left left).value) r hp
    exact ⟨m,hm,he,he⟩
  exact ⟨staticEq_of_decrypt_check_transport names HistoricalFrameSPOT.fixture_names_fresh left left h h,
    LocalRootSPOT.remaining_transport_diagonal.2⟩

end ExplainableCrypto.Helios.Symbolic.PaddedMinimumSPOT
