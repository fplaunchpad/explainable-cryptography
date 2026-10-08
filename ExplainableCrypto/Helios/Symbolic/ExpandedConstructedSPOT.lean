import ExplainableCrypto.Helios.Symbolic.ExpandedConstructedCompression
import ExplainableCrypto.Helios.Symbolic.ExpandedConstructedExperiments
import ExplainableCrypto.Helios.Symbolic.ExpandedMulMinimumSPOT
import ExplainableCrypto.Helios.Symbolic.ExpandedCipherKeySPOT

namespace ExplainableCrypto.Helios.Symbolic.ExpandedConstructedSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []
abbrev key : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
abbrev nonce : Recipe (ExpandedHandles 1) := .var (expandedPartial 1)
abbrev payload : Recipe (ExpandedHandles 1) := .var (expandedResult 1)
abbrev constructed : Recipe (ExpandedHandles 1) := .ternary .penc key nonce payload
abbrev a : CiphertextAssembly 1 (ExpandedHandles 1) := .constructed key nonce (.const .zero)
abbrev b : CiphertextAssembly 1 (ExpandedHandles 1) := .constructed key nonce (.const .one)
abbrev product : Recipe (ExpandedHandles 1) := (a.mul b).recipeWith expandedOld
abbrev compressed : Recipe (ExpandedHandles 1) := .ternary .penc key (.binary .compose nonce nonce) (.const .one)

private theorem compression : EqE product compressed :=
  (RootStep.homomorphic _ _ _ _ _).sound.trans (.ternary .penc (.refl _) (.refl _) (.equation .zero_one))
private theorem compressed_minimum (swap : Bool) (l r : CandidateSubstitution 1 Empty) :
    MinimalRecipe names.restricted (expandedFrame names swap l r []).value compressed := by
  have hm (v : Fin (ExpandedHandles 1)) : MinimalRecipe names.restricted (expandedFrame names swap l r []).value (.var v) :=
    .of_nodeCount_one trivial rfl
  have hn := accepted_expanded_results_numeric names HistoricalFrameSPOT.fixture_names_fresh l r [] (by simp) trivial swap
  have hc := expanded_minimum_compose_of_children names swap l r [] hn names.restricted nonce nonce
    (hm (expandedPartial 1)) (hm (expandedPartial 1))
  exact accepted_expanded_minimum_penc_of_children names HistoricalFrameSPOT.fixture_names_fresh swap l r []
    (by simp) trivial key (.binary .compose nonce nonce) (.const .one) (hm (expandedPartial 0)) hc (.of_nodeCount_one trivial rfl)

/-- A constructor using actual partial keys/nonces and a result payload is a
four-node global minimum and is shared without any smaller-test premise. -/
theorem published_constructor_minimum (swap swap' : Bool) :
    MinimalRecipe names.restricted (world swap).value constructed ∧ constructed.nodeCount = 4 ∧
      Frame.SharedMinimum (world swap) (world swap') constructed := by
  have hm : MinimalRecipe names.restricted (world swap).value constructed :=
    accepted_expanded_minimum_penc_of_children names HistoricalFrameSPOT.fixture_names_fresh swap left right []
      (by simp) trivial key nonce payload (.of_nodeCount_one trivial rfl) (.of_nodeCount_one trivial rfl) (.of_nodeCount_one trivial rfl)
  exact ⟨hm,rfl,accepted_expanded_minimum_children_penc_shared names HistoricalFrameSPOT.fixture_names_fresh
    swap swap' left right [] (by simp) trivial key nonce payload (.of_nodeCount_one trivial rfl)
      (.of_nodeCount_one trivial rfl) (.of_nodeCount_one trivial rfl)⟩

/-- A public partial can be a constructed nonce but cannot equal an honest
nonce combination. Opaque public provenance excludes the borrowed class. -/
theorem opaque_nonce_provenance (swap : Bool) :
    let g : CiphertextGroup 1 (ExpandedHandles 1) := .constructed nonce payload
    EqE (g.nonce names (world swap)) ((world swap).eval nonce) ∧
      ¬ EqE (combinationNonce names (.leaf (0,0))) ((world swap).eval nonce) := by
  refine ⟨.refl _,?_⟩
  intro he
  obtain ⟨u,v,hg⟩ := (CiphertextGroup.honest (handles := ExpandedHandles 1) (Combination.leaf (0,0))).constructed_of_public_nonce_of_opaque
    names (world swap) (expanded_frame_opaque_protected names swap left right [] (by simp))
    (fun i => Finset.mem_union_right _ (names.nonce_mem_nonceNames i.1 i.2)) nonce trivial he
  cases hg

/-- The public constructor cannot alias a cheaper honest ciphertext selector.
This rules out a spurious minimum result based only on component costs. -/
theorem no_cheaper_honest_alias (swap : Bool) :
    ¬ EqE ((world swap).eval constructed) ((world swap).eval (.unary .fst (.var (expandedOld 1)))) := by
  intro he
  exact (published_constructor_minimum swap swap).1.no_smaller
    (s := .unary .fst (.var (expandedOld 1))) trivial he (by decide)

/-- A singleton compression is unchanged and cannot be strictly smaller. -/
theorem singleton_boundary :
    let t : CiphertextAssembly 1 (ExpandedHandles 1) := .constructed key nonce payload
    t.recipeWith expandedOld = .ternary .penc (t.keyRecipeWith expandedOld) nonce payload ∧
      ¬ (Term.ternary .penc (t.keyRecipeWith expandedOld) nonce payload).nodeCount < (t.recipeWith expandedOld).nodeCount :=
  ⟨rfl,by decide⟩

/-- Repeated public nonce occurrences are retained. E3 and the numeric payload
law yield a six-node global shared minimum for a nine-node product in both
actual different-vote assignments. -/
theorem repeated_nonce_shared_compression (swap swap' : Bool) :
    product.nodeCount = 9 ∧ compressed.nodeCount = 6 ∧
    (Term.binary .compose nonce nonce).composeLeaves.card = 2 ∧
    EqE ((world swap).eval product) ((world swap).eval compressed) ∧
    Frame.SharedMinimum (world swap) (world swap') product ∧
    ¬ MinimalRecipe names.restricted (world swap).value product := by
  have hm := compressed_minimum swap left right
  exact ⟨rfl,rfl,rfl,compression.subst _,.of_recipe_eqE hm compression,
    fun h => h.no_smaller hm.isPublic (compression.subst _) (by decide)⟩

/-- The constructed branch's exact two-way induction interface is inhabited.
It produces a six-node shared minimum for a nonminimum parent; diagonal
candidates supply the smaller-minimum hypotheses without assuming B8. -/
theorem two_way_constructed_transport :
    let φ := expandedFrame names false left left []
    let ψ := expandedFrame names true left left []
    ∃ m, MinimalRecipe names.restricted φ.value m ∧ EqE (φ.eval product) (φ.eval m) ∧
      EqE (ψ.eval product) (ψ.eval m) ∧ m.nodeCount = 6 ∧ ¬ MinimalRecipe names.restricted φ.value product := by
  let φ := expandedFrame names false left left []
  let ψ := expandedFrame names true left left []
  have hsmall : Frame.SharedMinimaBelow φ ψ product.nodeCount := by
    intro r hp _
    obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := φ.value) r hp
    exact ⟨m,hm,he,he⟩
  have hv : (φ.eval product).CiphertextValue := ⟨_,_,_,(RootStep.homomorphic _ _ _ _ _).sound⟩
  obtain ⟨m,hm,he,he'⟩ := accepted_expanded_constructed_mul_shared_of_two_way_minima names
    HistoricalFrameSPOT.fixture_names_fresh false true left left [] (by simp) trivial a b
    ⟨⟨trivial,trivial,trivial⟩,⟨trivial,trivial,trivial⟩⟩ rfl hv hsmall hsmall
  have hmin := compressed_minimum false left left
  have heq := he.symm.trans (compression.subst φ.value)
  have hle := hm.least compressed hmin.isPublic heq
  have hge := hmin.least m hm.isPublic heq.symm
  refine ⟨m,hm,he,he',?_,fun h => h.no_smaller hmin.isPublic (compression.subst _) (by decide)⟩
  change m.nodeCount ≤ 6 at hle
  change 6 ≤ m.nodeCount at hge
  omega

/-- Unequal keys prevent full-E fusion; they cannot be ignored by compression. -/
theorem wrong_keys_do_not_compress :
    ¬ (Term.binary .mul (.ternary .penc (.name 40) (.name 50) (.const .zero))
      (.ternary .penc (.name 41) (.name 51) (.const .one)) : Ground).CiphertextValue :=
  ExpandedCipherKeySPOT.distinct_keys_do_not_fuse

/-- A reducible, four-node selected key is permitted. Compression preserves
its actual value and remains strict, even before minimizing the chosen key. -/
theorem delayed_key_compression (swap : Bool) :
    let delayed := Term.unary .fst (.binary .pair key (.const .bottom))
    let u : CiphertextAssembly 1 (ExpandedHandles 1) := .constructed delayed nonce (.const .zero)
    let t := u.mul b
    EqE ((world swap).eval (t.recipeWith expandedOld))
      ((world swap).eval (.ternary .penc delayed (.binary .compose nonce nonce) (.binary .add (.const .zero) (.const .one)))) ∧
      (t.recipeWith expandedOld).nodeCount = 12 ∧
      (Term.ternary .penc delayed (.binary .compose nonce nonce) (.binary .add (.const .zero) (.const .one))).nodeCount = 11 := by
  dsimp only
  let delayed := Term.unary .fst (.binary .pair key (.const .bottom))
  let u : CiphertextAssembly 1 (ExpandedHandles 1) := .constructed delayed nonce (.const .zero)
  have hv : ((world swap).eval ((u.mul b).recipeWith expandedOld)).CiphertextValue :=
    ⟨_,_,_,(EqE.binary .mul (.ternary .penc (.equation (.fst _ _)) (.refl _) (.refl _)) (.refl _)).trans
      (RootStep.homomorphic _ _ _ _ _).sound⟩
  exact ⟨expanded_constructed_compression_value names swap left right [] (u.mul b) rfl hv,rfl,rfl⟩

end ExplainableCrypto.Helios.Symbolic.ExpandedConstructedSPOT
