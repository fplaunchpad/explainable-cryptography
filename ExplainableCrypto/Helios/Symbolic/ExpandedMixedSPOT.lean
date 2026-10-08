import ExplainableCrypto.Helios.Symbolic.ExpandedGroupSPOT
import ExplainableCrypto.Helios.Symbolic.ExpandedMixedMinima
import ExplainableCrypto.Helios.Symbolic.ExpandedMixedExperiments
import ExplainableCrypto.Helios.Symbolic.ExpandedHonestSPOT
import ExplainableCrypto.Helios.Symbolic.ExpandedAddMinimumSPOT

namespace ExplainableCrypto.Helios.Symbolic.ExpandedMixedSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []
abbrev trustee : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
abbrev honest : Combination (HonestIndex 1) := .leaf (0,0)
abbrev publicA : CiphertextAssembly 1 (ExpandedHandles 1) := .constructed (.var (expandedOld 0)) trustee (.const .zero)
abbrev publicB : CiphertextAssembly 1 (ExpandedHandles 1) := .constructed (.var (expandedOld 0)) trustee (.const .one)
abbrev tree : CiphertextAssembly 1 (ExpandedHandles 1) := .mul publicA (.mul publicB (.honest (0,0)))
abbrev nonce : Recipe (ExpandedHandles 1) := .binary .compose trustee trustee
abbrev grouped : Recipe (ExpandedHandles 1) := mixedCombinationRecipeWith expandedOld nonce (.binary .add (.const .zero) (.const .one)) honest
abbrev shortest : Recipe (ExpandedHandles 1) := mixedCombinationRecipeWith expandedOld nonce (.const .one) honest

private theorem numeric (swap : Bool) (l r : CandidateSubstitution 1 Empty) : ExpandedResultsNumeric names swap l r [] :=
  accepted_expanded_results_numeric names HistoricalFrameSPOT.fixture_names_fresh l r [] (by simp) trivial swap
private theorem value (swap : Bool) (l r : CandidateSubstitution 1 Empty) :
    ((expandedFrame names swap l r []).eval (tree.recipeWith expandedOld)).CiphertextValue := by
  have h := tree.grouped_valueWith names _ expandedOld swap l r (expanded_honest_selector_value names swap l r [])
    (publicKey names) (by
      refine ⟨?_,?_,.refl _⟩
      all_goals rw [← expanded_election_handle_value names swap l r []]; exact .refl _)
  exact ⟨_,_,_,h⟩
private theorem minimum (swap : Bool) (l r : CandidateSubstitution 1 Empty) :
    MinimalRecipe names.restricted (expandedFrame names swap l r []).value shortest := by
  have hn := expanded_minimum_compose_of_children names swap l r [] (numeric swap l r) names.restricted trustee trustee
    (.of_nodeCount_one trivial rfl) (.of_nodeCount_one trivial rfl)
  exact expanded_minimum_mixed_of_minimum_nonce_atomic_payload names HistoricalFrameSPOT.fixture_names_fresh swap l r []
    (by simp) (numeric swap l r) nonce (.const .one) hn trivial rfl honest
private theorem compression (swap : Bool) (l r : CandidateSubstitution 1 Empty) :
    EqE ((expandedFrame names swap l r []).eval (tree.recipeWith expandedOld))
      ((expandedFrame names swap l r []).eval shortest) :=
  (expanded_mixed_compression_value names swap l r [] tree rfl (value swap l r)).trans
    (.binary .mul (.ternary .penc (.refl _) (.refl _) (.equation .zero_one)) (.refl _))

/-- Two public constructors and one honest selector cost twelve nodes. Mixed
grouping costs eleven; numeric simplification gives a nine-node global shared
minimum retaining both public partial nonce occurrences. -/
theorem published_mixed_shared_minimum (swap swap' : Bool) :
    tree.constructedCount=2 ∧ (tree.recipeWith expandedOld).nodeCount=12 ∧ grouped.nodeCount=11 ∧
    shortest.nodeCount=9 ∧ MinimalRecipe names.restricted (world swap).value shortest ∧
    Frame.SharedMinimum (world swap) (world swap') (tree.recipeWith expandedOld) ∧
    ¬ MinimalRecipe names.restricted (world swap).value (tree.recipeWith expandedOld) :=
  ⟨rfl,rfl,rfl,rfl,minimum swap left right,⟨shortest,minimum swap left right,compression swap left right,compression swap' left right⟩,
    fun hm => hm.no_smaller (minimum swap left right).isPublic (compression swap left right) (by decide)⟩

/-- A single constructor with published nonce/result payload is already a
seven-node global minimum. Mixed grouping is not always strictly smaller. -/
theorem single_constructor_strictness_refuted (swap : Bool) :
    let t : CiphertextAssembly 1 (ExpandedHandles 1) :=
      .mul (.constructed (.var (expandedOld 0)) trustee (.var (expandedResult 1))) (.honest (0,0))
    t.constructedCount=1 ∧ (t.recipeWith expandedOld).nodeCount=7 ∧
    ¬ (mixedCombinationRecipeWith expandedOld trustee (.var (expandedResult 1)) honest).nodeCount < (t.recipeWith expandedOld).nodeCount ∧
    MinimalRecipe names.restricted (world swap).value (t.recipeWith expandedOld) :=
  ⟨rfl,rfl,by decide,expanded_minimum_mixed_of_minimum_nonce_atomic_payload names HistoricalFrameSPOT.fixture_names_fresh
    swap left right [] (by simp) (numeric swap left right) trustee (.var (expandedResult 1))
      (.of_nodeCount_one trivial rfl) trivial rfl honest⟩

/-- Every minimum competitor of the concrete mixed product has one constructor,
one honest occurrence and exact nine-node cost. Arbitrary new-handle syntax is allowed. -/
theorem competitor_origin_and_cost (swap : Bool) (m : Recipe (ExpandedHandles 1))
    (hm : MinimalRecipe names.restricted (world swap).value m)
    (he : EqE ((world swap).eval m) ((world swap).eval shortest)) :
    (∃ t : CiphertextAssembly 1 (ExpandedHandles 1), ∃ s q b,
      t.recipeWith expandedOld=m ∧ t.group=.mixed s q b ∧ t.constructedCount=1 ∧ b.indices=honest.indices) ∧
      m.nodeCount=9 := by
  obtain ⟨t,s,q,b,ht,hg,hcount,hi,_,_,_⟩ := expanded_minimum_mixed_combination_origin names HistoricalFrameSPOT.fixture_names_fresh
    swap left right [] (by simp) (numeric swap left right) nonce (.const .one) ⟨trivial,trivial⟩ trivial honest m hm he
  have h₁ := hm.least shortest (minimum swap left right).isPublic he
  have h₂ := (minimum swap left right).least m hm.isPublic he.symm
  exact ⟨⟨t,s,q,b,ht,hg,hcount,hi⟩,by change m.nodeCount ≤ 9 at h₁; change 9 ≤ m.nodeCount at h₂; omega⟩

/-- The exact simultaneous-induction interface is inhabited by diagonal
candidates. It yields a nine-node shared minimum for a twelve-node input. -/
theorem two_way_mixed_transport :
    let φ := expandedFrame names false left left []
    let ψ := expandedFrame names true left left []
    ∃ m, MinimalRecipe names.restricted φ.value m ∧ EqE (φ.eval (tree.recipeWith expandedOld)) (φ.eval m) ∧
      EqE (ψ.eval (tree.recipeWith expandedOld)) (ψ.eval m) ∧ m.nodeCount=9 := by
  let φ := expandedFrame names false left left []
  let ψ := expandedFrame names true left left []
  have hsmall : Frame.SharedMinimaBelow φ ψ (tree.recipeWith expandedOld).nodeCount := by
    intro r hp _
    obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := φ.value) r hp
    exact ⟨m,hm,he,he⟩
  obtain ⟨m,hm,he,he'⟩ := accepted_expanded_mixed_compression_shared_of_two_way_minima names HistoricalFrameSPOT.fixture_names_fresh
    false true left left [] (by simp) trivial tree ⟨⟨trivial,trivial,trivial⟩,⟨⟨trivial,trivial,trivial⟩,trivial⟩⟩ rfl
    (value false left left) (by decide) hsmall hsmall
  have hmin := minimum false left left
  have heq := he.symm.trans (compression false left left)
  have h₁ := hm.least shortest hmin.isPublic heq
  have h₂ := hmin.least m hm.isPublic heq.symm
  exact ⟨m,hm,he,he',by change m.nodeCount ≤ 9 at h₁; change 9 ≤ m.nodeCount at h₂; omega⟩

/-- Honest duplicate occurrences survive mixed compression in the actual
published frame; the original opaque nonce control supplies the negative. -/
theorem honest_duplicates_required (swap : Bool) :
    let twice : Combination (HonestIndex 1) := .mul honest honest
    (combinationRecipeWith (handles := ExpandedHandles 1) expandedOld twice).nodeCount=5 ∧
    ¬ EqE ((world swap).eval (mixedCombinationRecipeWith expandedOld trustee (.const .zero) honest))
      ((world swap).eval (mixedCombinationRecipeWith expandedOld trustee (.const .zero) twice)) := by
  refine ⟨rfl,?_⟩
  intro he
  have h₁ := expanded_mixedCombination_value names swap left right [] trustee (.const .zero) honest
  have h₂ := expanded_mixedCombination_value names swap left right [] trustee (.const .zero) (.mul honest honest)
  exact ExpandedGroupSPOT.duplicate_honest_nonce_retained swap
    (((EqE.penc_iff _ _ _ _ _ _).mp (h₁.symm.trans (he.trans h₂))).2.1)

/-- An honest contribution is necessary to force election-key agreement.
An unrelated constructed-only key is supported, but the gate's actual partial
key cannot fuse with an honest election-key ciphertext. -/
theorem honest_contribution_required_for_key_binding (swap : Bool) :
    let t : CiphertextAssembly 1 (ExpandedHandles 1) := .constructed (.name 40) trustee (.const .zero)
    let bad : CiphertextAssembly 1 (ExpandedHandles 1) :=
      .mul (.constructed trustee (.name 40) (.const .zero)) (.honest (0,0))
    t.KeyAgreement names (world swap) (.name 40) ∧
      ¬ EqE (publicKey names) ((world swap).eval (t.keyRecipeWith expandedOld)) ∧
      ¬ ((world swap).eval (bad.recipeWith expandedOld)).CiphertextValue := by
  refine ⟨.refl _,?_,?_⟩
  · intro he
    obtain ⟨u,hu,_⟩ := he.pk_irreducible_shape (name_irreducible 40)
    cases hu
  · intro hv
    obtain ⟨k,nr,m,he⟩ := hv
    let bad : CiphertextAssembly 1 (ExpandedHandles 1) :=
      .mul (.constructed trustee (.name 40) (.const .zero)) (.honest (0,0))
    have hk := bad.key_agreement_of_valueWith names (world swap) expandedOld swap left right
      (expanded_honest_selector_value names swap left right []) he
    have hpk : EqE (publicKey names) ((world swap).eval trustee) := hk.2.trans hk.1.symm
    have hs := expanded_projection_pk_origin names swap left right [] (numeric swap left right)
      (expandedPartial 0) .handle hpk.symm
    exact (by decide : (Term.var (expandedPartial 0) : Recipe (ExpandedHandles 1)) ≠ .var (expandedOld 0)) hs

abbrev paddedPayload : Recipe (ExpandedHandles 1) := .binary .add (.name 40) (.var (expandedResult 0))
abbrev singlePadded : Recipe (ExpandedHandles 1) := mixedCombinationRecipeWith expandedOld trustee paddedPayload honest
abbrev singleShort : Recipe (ExpandedHandles 1) := mixedCombinationRecipeWith expandedOld trustee (.name 40) honest
private theorem public40 : (Term.name (V := Fin (ExpandedHandles 1)) 40).Public names.restricted := by
  change 40 ∉ names.restricted; decide
private theorem single_short_minimum (swap : Bool) : MinimalRecipe names.restricted (world swap).value singleShort :=
  expanded_minimum_mixed_of_minimum_nonce_atomic_payload names HistoricalFrameSPOT.fixture_names_fresh swap left right []
    (by simp) (numeric swap left right) trustee (.name 40) (.of_nodeCount_one trivial rfl) public40 rfl honest
private theorem single_padded_value (swap : Bool) : EqE ((world swap).eval singlePadded) ((world swap).eval singleShort) := by
  have hz : EqE ((world swap).eval (.var (expandedResult 0))) (.const .zero) := by
    rw [Frame.eval,Term.subst,expanded_frame_result]
    exact SharedTallySPOT.nonliteral_two_candidate_tally.1 swap
  have hpad : EqE ((world swap).eval (.binary .add paddedPayload (.const .zero)))
      ((world swap).eval (.binary .add (.name 40) (.const .zero))) :=
    (EqE.binary .add (.binary .add (.refl _) hz) (.refl _)).trans
      ((EqE.equation (.assoc .add trivial _ _ _)).trans (.binary .add (.refl _) (.equation .zero_zero)))
  have h := (expanded_group_ciphertext_eq_iff names HistoricalFrameSPOT.fixture_names_fresh swap left right [] (by simp)
    (.mixed trustee paddedPayload honest) (.mixed trustee (.name 40) honest) ⟨trivial,public40,trivial⟩ ⟨trivial,public40⟩
    (publicKey names) (publicKey names)).mpr ⟨.refl _,rfl,.refl _,hpad⟩
  exact (expanded_mixedCombination_value names swap left right [] trustee paddedPayload honest).trans
    (h.trans (expanded_mixedCombination_value names swap left right [] trustee (.name 40) honest).symm)

/-- The one-constructor padding regression: minimum immediate children can
form a nonminimum nine-node mixed parent. Its published zero is
absorbed beside the honest numeric payload, giving a seven-node shared minimum. -/
theorem one_constructor_payload_problem (swap swap' : Bool) :
    Frame.MinimumChildren (world swap) singlePadded ∧
    ¬ MinimalRecipe names.restricted (world swap).value singlePadded ∧
    singlePadded.nodeCount=9 ∧ singleShort.nodeCount=7 ∧
    Frame.SharedMinimum (world swap) (world swap') singlePadded := by
  have hpayload := (ExpandedAddMinimumSPOT.zero_and_duplicate_global_minima swap).1
  have hc := accepted_expanded_minimum_penc_of_children names HistoricalFrameSPOT.fixture_names_fresh swap left right []
    (by simp) trivial (.var (expandedOld 0)) trustee paddedPayload (.of_nodeCount_one trivial rfl) (.of_nodeCount_one trivial rfl) hpayload
  have hh := accepted_expanded_minimum_honest_combination names HistoricalFrameSPOT.fixture_names_fresh swap left right []
    (by simp) trivial honest
  exact ⟨⟨hc,hh⟩,fun hm => hm.no_smaller (single_short_minimum swap).isPublic (single_padded_value swap) (by decide),rfl,rfl,
    ⟨singleShort,single_short_minimum swap,single_padded_value swap,single_padded_value swap'⟩⟩

/-- The exact-size minimum grouped representative theorem applies to a
concrete minimum mixed tree whose constructor is on the right. -/
theorem minimum_regrouping_preserves_exact_size (swap : Bool) :
    let t : CiphertextAssembly 1 (ExpandedHandles 1) := .mul (.honest (0,0)) publicA
    MinimalRecipe names.restricted (world swap).value (t.recipeWith expandedOld) ∧
      t.constructedCount=1 ∧
      (mixedCombinationRecipeWith expandedOld trustee (.const .zero) honest).nodeCount=(t.recipeWith expandedOld).nodeCount := by
  let t : CiphertextAssembly 1 (ExpandedHandles 1) := .mul (.honest (0,0)) publicA
  have hm := expanded_minimum_mixed_of_minimum_nonce_atomic_payload names HistoricalFrameSPOT.fixture_names_fresh swap left right []
    (by simp) (numeric swap left right) trustee (.const .zero) (.of_nodeCount_one trivial rfl) trivial rfl honest
  have he : EqE (t.recipeWith expandedOld) (mixedCombinationRecipeWith expandedOld trustee (.const .zero) honest) :=
    .equation (.comm .mul trivial _ _)
  have ht := hm.of_equivalent_size (show (t.recipeWith expandedOld).Public names.restricted from ⟨trivial,trivial,trivial,trivial⟩)
    (he.subst _ ) (by decide)
  have hv : ((world swap).eval (t.recipeWith expandedOld)).CiphertextValue :=
    ⟨_,_,_,(he.subst _).trans (expanded_mixedCombination_value names swap left right [] trustee (.const .zero) honest)⟩
  exact ⟨ht,expanded_minimum_mixed_constructedCount_eq_one names swap left right [] t ht rfl hv,
    (expanded_minimum_mixed_grouped_representative names swap left right [] t ht rfl hv).2⟩

end ExplainableCrypto.Helios.Symbolic.ExpandedMixedSPOT
