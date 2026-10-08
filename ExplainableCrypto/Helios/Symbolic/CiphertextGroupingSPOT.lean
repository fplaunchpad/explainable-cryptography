import ExplainableCrypto.Helios.Symbolic.CiphertextGroupingSoundness
import ExplainableCrypto.Helios.Symbolic.MixedCiphertextSPOT

namespace ExplainableCrypto.Helios.Symbolic.CiphertextGroupingSPOT
open Historical General
abbrev names := MixedCiphertextSPOT.names
abbrev left := MixedCiphertextSPOT.left
abbrev right := MixedCiphertextSPOT.right
abbrev world := MixedCiphertextSPOT.world
abbrev wrappedKey : Recipe 3 := .unary .fst (.binary .pair (.var 0) (.const .bottom))
abbrev first : CiphertextAssembly 1 := .constructed wrappedKey (.name 40) (.name 80)
abbrev second : CiphertextAssembly 1 := .constructed (.var 0) (.name 41) (.const .zero)
abbrev honest : CiphertextAssembly 1 := .honest (0, 1)
abbrev assembly : CiphertextAssembly 1 := .mul (.mul honest first) (.mul second honest)
abbrev occurrences : Combination (HonestIndex 1) := .mul (.leaf (0, 1)) (.leaf (0, 1))
abbrev nonce : Recipe 3 := .binary .compose (.name 40) (.name 41)
abbrev payload : Recipe 3 := .binary .add (.name 80) (.const .zero)
abbrev canonical : Recipe 3 := mixedCombinationRecipe nonce payload occurrences

private theorem agreement (swap : Bool) : assembly.KeyAgreement names (world swap) (publicKey names) :=
  ⟨⟨.refl _, (RootStep.fst _ _).sound⟩, ⟨.refl _, .refl _⟩⟩

/-- Literal regrouping keeps two distinct public contributions and two
occurrences of the same honest ciphertext. -/
theorem exact_group_and_original_bounds :
    assembly.group = .mixed nonce payload occurrences ∧
    assembly.recipe.nodeCount = 20 ∧ assembly.group.budget = 9 ∧
    nonce.nodeCount < assembly.recipe.nodeCount ∧
    (Term.binary .add payload (.const .zero)).nodeCount < assembly.recipe.nodeCount := by
  have h := assembly.mixed_observations_smaller (rfl : assembly.group = .mixed nonce payload occurrences)
  exact ⟨rfl, by decide, by decide, h.1, h.2⟩

theorem syntactically_different_keys_agree (swap : Bool) :
    wrappedKey ≠ (Term.var 0 : Recipe 3) ∧
    EqE ((world swap).eval wrappedKey) ((world swap).eval (.var 0)) ∧
    assembly.KeyAgreement names (world swap) (publicKey names) :=
  ⟨by decide, (RootStep.fst _ _).sound, agreement swap⟩

theorem assembly_and_group_are_public :
    assembly.recipe.Public names.restricted ∧ assembly.group.Public names.restricted ∧
    assembly.keyRecipe.Public names.restricted ∧ assembly.keyRecipe.nodeCount < assembly.recipe.nodeCount := by
  have hp : assembly.recipe.Public names.restricted := by
    simp only [wrappedKey, CiphertextAssembly.recipe, Term.project, Term.drop, Term.Public]
    decide
  exact ⟨hp, assembly.group_public hp, assembly.keyRecipe_public hp, assembly.keyRecipe_smaller⟩

/-- Actual full-E frame values agree with the independently written mixed recipe,
including reducible honest candidate terms and the projection-wrapped key. -/
theorem grouped_actual_value (swap : Bool) :
    EqE ((world swap).eval assembly.recipe) ((world swap).eval canonical) :=
  (assembly.grouped_value names swap left right (publicKey names) (agreement swap)).trans
    (mixedCombination_value names swap left right nonce payload occurrences).symm

/-- Deleting a constructed contribution is observable even when the honest bag
and public payload are kept fixed. -/
theorem dropped_public_factor_rejected (swap : Bool) :
    ¬ EqE ((world swap).eval assembly.recipe)
      ((world swap).eval (mixedCombinationRecipe (.name 40) payload occurrences)) := by
  intro he
  have hc := (grouped_actual_value swap).symm.trans he
  have hn := ((mixedCombination_equality_iff names HistoricalFrameSPOT.fixture_names_fresh swap left right
    nonce payload (.name 40) payload
    (by change 40 ∉ names.nonceNames ∧ 41 ∉ names.nonceNames; decide)
    (by change 40 ∉ names.nonceNames; decide) occurrences occurrences).mp hc).2.1
  exact arithmetic_not_eqE_name .compose (Or.inr rfl) _ _ _ hn

abbrev wrongKey : CiphertextAssembly 1 :=
  .mul honest (.constructed (.name 50) (.name 40) (.name 80))

/-- Publicness alone does not justify fusion; a wrong-key leaf rules out every
ciphertext target, not just the expected nonce or payload. -/
theorem wrong_key_cannot_fuse (swap : Bool) :
    wrongKey.recipe.Public names.restricted ∧
    ∀ k r p : Ground, ¬ EqE ((world swap).eval wrongKey.recipe) (.ternary .penc k r p) := by
  refine ⟨?_, ?_⟩
  · simp only [CiphertextAssembly.recipe, Term.project, Term.drop, Term.Public]
    decide
  intro k r p he
  have hk := wrongKey.key_agreement_of_value names swap left right he
  have hc : EqE (publicKey names) (.name 50) := hk.1.trans hk.2.symm
  obtain ⟨_, hshape, _⟩ := hc.pk_irreducible_shape (name_irreducible 50)
  cases hshape

/-- Honest-only input remains honest-only. Padding its nonce with zero would
change its E-value because composition has no identity law. -/
theorem honest_group_inserts_no_unit (swap : Bool) :
    honest.group = .honest (.leaf (0, 1)) ∧
    ¬ EqE ((world swap).eval honest.recipe)
      (.ternary .penc (publicKey names) (.binary .compose (.const .zero) (.name 21))
        (combinationMessage swap left right (.leaf (0, 1)))) := by
  refine ⟨rfl, ?_⟩
  intro he
  have hv := honest.grouped_value names swap left right (publicKey names) (EqE.refl _)
  have hn := ((EqE.penc_iff _ _ _ _ _ _).mp (hv.symm.trans he)).2.1
  exact arithmetic_not_eqE_name .compose (Or.inr rfl) _ _ _ hn.symm

/-- A public-only group does not acquire payload padding. That change is visible
until an honest numeric contribution is actually present. -/
theorem constructed_group_inserts_no_zero (swap : Bool) :
    first.group = .constructed (.name 40) (.name 80) ∧
    ¬ EqE ((world swap).eval first.recipe)
      ((world swap).eval (.ternary .penc (.var 0) (.name 40) payload)) := by
  refine ⟨rfl, ?_⟩
  intro he
  have hv := first.grouped_value names swap left right (publicKey names) (RootStep.fst _ _).sound
  have hm := ((EqE.penc_iff _ _ _ _ _ _).mp (hv.symm.trans he)).2.2
  exact arithmetic_not_eqE_name .add (Or.inl rfl) _ _ _ hm.symm

/-- The complete minimum-origin bridge is inhabited in the fresh actual frame.
Minimum existence preserves the original value and full public-name policy. -/
theorem minimum_grouping_is_inhabited (swap : Bool) :
    ∃ r : Recipe 3, ∃ t : CiphertextAssembly 1,
      MinimalRecipe names.restricted (world swap).value r ∧ t.recipe = r ∧
      EqE ((world swap).eval assembly.recipe) ((world swap).eval r) ∧
      t.group.Public names.restricted ∧ t.group.budget ≤ r.nodeCount ∧
      t.keyRecipe.Public names.restricted ∧ t.keyRecipe.nodeCount < r.nodeCount ∧
      EqE ((world swap).eval t.keyRecipe) (publicKey names) := by
  obtain ⟨r, hm, he⟩ := exists_minimal_recipe (σ := (world swap).value)
    assembly.recipe assembly_and_group_are_public.1
  have hv := he.symm.trans (assembly.grouped_value names swap left right (publicKey names) (agreement swap))
  obtain ⟨t, ht, _, hp, hb, hkp, hks, hkv, _, _⟩ :=
    minimum_ciphertext_grouping names swap left right names.restricted r hm hv
  exact ⟨r, t, hm, ht, he, hp, hb, hkp, hks, hkv⟩

end ExplainableCrypto.Helios.Symbolic.CiphertextGroupingSPOT
