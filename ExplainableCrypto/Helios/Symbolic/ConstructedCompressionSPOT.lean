import ExplainableCrypto.Helios.Symbolic.ConstructedCompression
import ExplainableCrypto.Helios.Symbolic.ConstructedCompressionExperiments

namespace ExplainableCrypto.Helios.Symbolic.ConstructedCompressionSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world := LocalRootSPOT.world
abbrev key := LocalRootSPOT.key
abbrev wrappedKey : Recipe 3 := .unary .fst (.binary .pair key (.const .bottom))
abbrev a : CiphertextAssembly 1 := .constructed key (.name 40) (.const .zero)
abbrev b : CiphertextAssembly 1 := .constructed wrappedKey (.name 41) (.const .one)
abbrev nonce : Recipe 3 := .binary .compose (.name 40) (.name 41)
abbrev payload : Recipe 3 := .binary .add (.const .zero) (.const .one)
abbrev compressed : Recipe 3 := .ternary .penc key nonce payload
abbrev minimumCipher : Recipe 3 := .ternary .penc key nonce (.const .one)

private theorem public40 : (Term.name (V := Fin 3) 40).Public names.restricted := by
  change 40 ∉ names.restricted; decide
private theorem public41 : (Term.name (V := Fin 3) 41).Public names.restricted := by
  change 41 ∉ names.restricted; decide
private theorem coherent (swap : Bool) : (a.mul b).Coherent (world swap) :=
  ⟨trivial,trivial,(RootStep.fst _ _).sound.symm⟩
private theorem public_tree (swap : Bool) : (a.mul b).recipe.Public names.restricted := by
  have hk := (LocalRootSPOT.nested_constructor_minima swap).2.1.isPublic
  exact ⟨⟨hk,public40,trivial⟩,⟨⟨hk,trivial⟩,public41,trivial⟩⟩

/-- A four-node key and a removable key wrapper give eighteen raw nodes.
Fusion alone gives eleven; numeric collapse gives a nine-node shared minimum. -/
theorem non_atomic_compression_and_shared_minimum (swap : Bool) :
    (a.mul b).recipe.nodeCount = 18 ∧ compressed.nodeCount = 11 ∧
    compressed.nodeCount < (a.mul b).recipe.nodeCount ∧
    EqE ((world swap).eval (a.mul b).recipe) ((world swap).eval compressed) ∧
    MinimalRecipe names.restricted (world swap).value minimumCipher ∧
    minimumCipher.nodeCount = 9 ∧
    Frame.SharedMinimum (world swap) (world (!swap)) (a.mul b).recipe := by
  have he (s : Bool) : EqE ((world s).eval (a.mul b).recipe) ((world s).eval minimumCipher) :=
    ((a.mul b).constructed_compression_value names s left right rfl (coherent s)).trans
      (.ternary .penc (.refl _) (.refl _) (.equation .zero_one))
  have hn := minimum_compose_of_children names swap left right names.restricted _ _
    (.of_nodeCount_one public40 rfl) (.of_nodeCount_one public41 rfl)
  have hm := minimum_penc_of_children names swap left right key nonce (.const .one)
    (LocalRootSPOT.nested_constructor_minima swap).2.1 hn (.of_nodeCount_one trivial rfl)
  exact ⟨rfl,rfl,a.constructed_mul_compression_smaller b rfl,
    (a.mul b).constructed_compression_value names swap left right rfl (coherent swap),
    hm,rfl,⟨minimumCipher,hm,he swap,he (!swap)⟩⟩

/-- A singleton is already the same constructor; strict decrease needs a
multiplication root. The singleton in this fixture is globally minimum. -/
theorem singleton_strictness_refuted (swap : Bool) :
    a.recipe = .ternary .penc a.keyRecipe (.name 40) (.const .zero) ∧
    ¬ (Term.ternary .penc a.keyRecipe (.name 40) (.const .zero)).nodeCount < a.recipe.nodeCount ∧
    MinimalRecipe names.restricted (world swap).value a.recipe :=
  ⟨rfl,by decide,minimum_penc_of_children names swap left right _ _ _
    (LocalRootSPOT.nested_constructor_minima swap).2.1
    (.of_nodeCount_one public40 rfl) (.of_nodeCount_one trivial rfl)⟩

abbrev wrong : CiphertextAssembly 1 := .mul
  (.constructed (.name 40) (.name 41) (.const .zero))
  (.constructed (.name 42) (.name 43) (.const .one))

/-- Different keys cannot be fused to any single ciphertext, despite the
pure syntax grouping returning a constructed group. -/
theorem wrong_key_fusion_refuted (swap : Bool) :
    (∃ r p, wrong.group = .constructed r p) ∧
    ¬ ((world swap).eval wrong.recipe).CiphertextValue := by
  refine ⟨⟨_,_,rfl⟩,?_⟩
  intro hv
  have hc := (wrong.coherent_iff_ciphertext_value names swap left right).mpr hv
  have he := (EqE.name_iff 40 42).mp hc.2.2
  omega

def source : Frame names.restricted 3 := ⟨fun _ => .name 40⟩
def destination : Frame names.restricted 3 := ⟨fun _ => .name 42⟩
abbrev changing : CiphertextAssembly 1 := .mul
  (.constructed (.var 0) (.name 41) (.const .zero))
  (.constructed (.name 40) (.name 43) (.const .one))

/-- Source coherence cannot be silently reused in an arbitrary destination.
The failing premise is equality of the selected keys. -/
theorem destination_coherence_required : changing.Coherent source ∧ ¬ changing.Coherent destination := by
  refine ⟨⟨trivial,trivial,.refl _⟩,?_⟩
  intro hc
  have he := (EqE.name_iff 42 40).mp hc.2.2
  omega

/-- An honest contribution stays mixed and is excluded from this compression
theorem; it cannot be treated as a publicly constructed nonce. -/
theorem honest_contribution_excluded :
    ¬ ∃ r p, (a.mul (.honest (0,0))).group = .constructed r p := by
  rintro ⟨r,p,h⟩
  cases h

/-- The public-nonce minimum-origin theorem applies to every minimum
competitor of the nontrivial fixture, not just its chosen constructor. -/
theorem minimum_competitor_is_constructor (swap : Bool) (r : Recipe 3)
    (hm : MinimalRecipe names.restricted (world swap).value r)
    (he : EqE ((world swap).eval r) ((world swap).eval compressed)) :
    ∃ k nr p, r = .ternary .penc k nr p := by
  apply minimum_ciphertext_public_nonce_form names swap left right r nonce hm _ he
  exact ⟨by change 40 ∉ names.nonceNames; decide,by change 41 ∉ names.nonceNames; decide⟩

/-- Both conditional transport interfaces are inhabited on the diagonal.
The different-assignment fixture above separately checks an actual shared
minimum without assuming all smaller recipes already transfer. -/
theorem conditional_transport_diagonal (swap : Bool) :
    Frame.SharedMinimum (world swap) (world swap) (a.mul b).recipe := by
  apply constructed_mul_shared_of_smaller_observations names swap swap left right a b
    (public_tree swap) rfl (coherent swap)
  · intro r s _ _ _
    exact Iff.rfl
  · intro s hp _
    obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (world swap).value) s hp
    exact ⟨m,hm,he,he⟩

end ExplainableCrypto.Helios.Symbolic.ConstructedCompressionSPOT
