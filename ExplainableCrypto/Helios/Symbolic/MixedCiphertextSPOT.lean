import ExplainableCrypto.Helios.Symbolic.MixedCiphertexts
import ExplainableCrypto.Helios.Symbolic.NumericReflectionSPOT
import ExplainableCrypto.Helios.Symbolic.CiphertextCombinationSPOT

namespace ExplainableCrypto.Helios.Symbolic.MixedCiphertextSPOT
open Historical
abbrev names : Names 1 := HistoricalFrameSPOT.names
abbrev left := GeneralCandidateSPOT.represented
abbrev right := GeneralCandidateSPOT.abstain
abbrev world (swap : Bool) := General.frame names swap left right
abbrev rho : Recipe 3 := (Term.var 1).project 1
abbrev sigma : Recipe 3 := .unary .fst (.binary .pair rho (.const .bottom))
abbrev payload : Recipe 3 := .name 80
abbrev padded : Recipe 3 := .binary .add payload (.const .zero)
abbrev a := CiphertextCombinationSPOT.repeated
abbrev b := CiphertextCombinationSPOT.rearranged

private theorem nonce_subset : names.nonceNames ⊆ names.restricted := by
  intro x hx
  exact Finset.mem_union_right _ hx
private theorem rho_public : rho.Public names.restricted := trivial
private theorem sigma_public : sigma.Public names.restricted := ⟨rho_public, trivial⟩
private theorem nonce_public (r : Nat) (h : 40 ≤ r) : (Term.name r : Recipe 3).Public names.nonceNames := by
  change r ∉ names.nonceNames
  simp [names, HistoricalFrameSPOT.names, Names.nonceNames, Finset.mem_image]
  omega

private theorem same_remainder (swap : Bool) : EqE ((world swap).eval rho) ((world swap).eval sigma) :=
  (RootStep.fst ((world swap).eval rho) (.const .bottom)).sound.symm

/-- This public nonce recipe's raw value is unsafe, but has a protected E-value. -/
theorem raw_unsafe_public_remainder : rho.Public names.restricted ∧
    ((world false).eval rho).nonceSafe names.nonceNames = false ∧
    ProtectedValue names.nonceNames ((world false).eval rho) := by
  refine ⟨rho_public, by decide, ?_⟩
  exact General.frame_recipe_protected_value names false left right rho (rho_public.of_subset nonce_subset)

private theorem remainder_value (swap : Bool) :
    EqE ((world swap).eval rho)
      (.ternary .penc (publicKey names) (.name 21) (.const (if swap then .zero else .one))) := by
  have hv : EqE ((world swap).eval rho)
      (General.ciphertext names 0 (General.choice swap left right 0).value 1) := by
    simpa [world, Frame.eval, rho, Term.subst_project, Term.subst, General.frame] using
      General.ballot_project_ciphertext names 0 (General.choice swap left right 0).value (1 : Fin 2)
  cases swap with
  | false => exact hv.trans (.ternary .penc (.refl _) (.refl _) (.equation .zero_one))
  | true => exact hv

/-- Public remainders can change E-values across worlds; the reduction compares
pairs of subrecipes within each world, not pointwise values across worlds. -/
theorem public_remainder_values_differ : ¬ EqE ((world false).eval rho) ((world true).eval rho) := by
  intro he
  have hc := (remainder_value false).symm.trans (he.trans (remainder_value true))
  exact zero_not_one ((EqE.penc_iff _ _ _ _ _ _).mp hc).2.2.symm

theorem protected_mixed_nonces_equal (swap : Bool) :
    EqE (.binary .compose ((world swap).eval rho) (General.combinationNonce names a))
      (.binary .compose ((world swap).eval sigma) (General.combinationNonce names b)) :=
  (General.frame_mixed_nonce_eq_iff names HistoricalFrameSPOT.fixture_names_fresh swap swap left right
    rho sigma (rho_public.of_subset nonce_subset) (sigma_public.of_subset nonce_subset) a b).mpr
    ⟨by decide, same_remainder swap⟩

private theorem padding_equal (swap : Bool) :
    EqE ((world swap).eval (.binary .add payload (.const .zero)))
      ((world swap).eval (.binary .add padded (.const .zero))) :=
  (BaseEq.zero_padding_after_number (.name 80) 0).sound

/-- Equal mixed products retain a raw-unsafe public remainder, a changed tree,
repeated honest factors and the source zero-padding distinction. -/
theorem zero_padded_mixed_products_equal (swap : Bool) :
    EqE ((world swap).eval (General.mixedCombinationRecipe rho payload a))
      ((world swap).eval (General.mixedCombinationRecipe sigma padded b)) :=
  (General.mixedCombination_equality_iff names HistoricalFrameSPOT.fixture_names_fresh swap left right
    rho payload sigma padded (rho_public.of_subset nonce_subset) (sigma_public.of_subset nonce_subset) a b).mpr
    ⟨by decide, same_remainder swap, padding_equal swap⟩

theorem mixed_recipes_public :
    (General.mixedCombinationRecipe rho payload a).Public names.restricted ∧
      (General.mixedCombinationRecipe sigma padded b).Public names.restricted := by
  have hp : payload.Public names.restricted := by change 80 ∉ names.restricted; decide
  have hpad : padded.Public names.restricted := ⟨hp, trivial⟩
  exact ⟨General.mixedCombination_public _ _ rho_public hp _,
    General.mixedCombination_public _ _ sigma_public hpad _⟩

theorem smaller_observations_and_swap_step :
    (General.mixedCombinationRecipe rho payload a).nodeCount = 20 ∧
    rho.nodeCount < (General.mixedCombinationRecipe rho payload a).nodeCount ∧
    (Term.binary .add payload (.const .zero)).nodeCount < (General.mixedCombinationRecipe rho payload a).nodeCount ∧
    (EqE ((world false).eval (General.mixedCombinationRecipe rho payload a))
        ((world false).eval (General.mixedCombinationRecipe sigma padded b)) ↔
      EqE ((world true).eval (General.mixedCombinationRecipe rho payload a))
        ((world true).eval (General.mixedCombinationRecipe sigma padded b))) := by
  have hb := General.mixedCombination_subrecipe_bounds rho payload a
  refine ⟨by decide, hb.1, hb.2, ?_⟩
  exact General.mixedCombination_equality_swap_of_observations names HistoricalFrameSPOT.fixture_names_fresh
    left right rho payload sigma padded (rho_public.of_subset nonce_subset) (sigma_public.of_subset nonce_subset) a b
    (iff_of_true (same_remainder false) (same_remainder true))
    (iff_of_true (padding_equal false) (padding_equal true))

/-- Allowing restricted literal remainders can compensate for a different honest
index. The fresh name assignment alone does not justify decomposition. -/
theorem remainder_protection_required :
    EqE (Term.binary .compose (.name 21) (.name 20) : Ground) (.binary .compose (.name 20) (.name 21)) ∧
    (Combination.leaf (0, 0) : Combination (General.HonestIndex 1)).indices ≠ (Combination.leaf (0, 1)).indices ∧
    ¬ ProtectedValue names.nonceNames (Term.name (V := Empty) 21) := by
  refine ⟨.equation (.comm .compose trivial _ _), by decide, ?_⟩
  rintro ⟨r, he, hr⟩
  exact nonce_safe_not_eqE_name hr (by decide : 21 ∈ names.nonceNames) he.symm

/-- The numeric payload comparison succeeds, so this rejection is caused by
the independently changed public nonce remainder. -/
theorem changed_public_nonce_rejected (swap : Bool) :
    EqE ((world swap).eval (.binary .add payload (.const .zero)))
      ((world swap).eval (.binary .add padded (.const .zero))) ∧
    ¬ EqE ((world swap).eval (General.mixedCombinationRecipe (.name 40) payload a))
      ((world swap).eval (General.mixedCombinationRecipe (.name 41) padded a)) := by
  refine ⟨padding_equal swap, ?_⟩
  intro he
  have h := (General.mixedCombination_equality_iff names HistoricalFrameSPOT.fixture_names_fresh swap left right
    (.name 40) payload (.name 41) padded (nonce_public 40 (by omega)) (nonce_public 41 (by omega)) a a).mp he
  have hn := (EqE.name_iff _ _).mp h.2.1
  change 40 = 41 at hn
  omega

/-- Adding one to a payload remains observable in ciphertext equality. -/
theorem positive_payload_increment_rejected (swap : Bool) :
    ¬ EqE ((world swap).eval (General.mixedCombinationRecipe (.name 40) payload a))
      ((world swap).eval (General.mixedCombinationRecipe (.name 40) (.binary .add payload (.const .one)) a)) := by
  intro he
  have h := (General.mixedCombination_equality_iff names HistoricalFrameSPOT.fixture_names_fresh swap left right
    (.name 40) payload (.name 40) (.binary .add payload (.const .one))
    (nonce_public 40 (by omega)) (nonce_public 40 (by omega)) a a).mp he
  have hn := h.2.2.denote (fun _ => 0) (fun _ => 0)
  change 0 = 1 at hn
  omega

/-- Equal raw nonce-factor counts do not let a public construction match an
honest nonce. This control exercises protection rather than a count mismatch. -/
theorem public_constructor_same_count_rejected (swap : Bool) :
    (Term.binary .compose (.name 40) (.name 20) : Ground).composeFactors.card = 2 ∧
    (Term.binary .compose (.name 40) (.name 41) : Ground).composeFactors.card = 2 ∧
    ¬ EqE ((world swap).eval (General.mixedCombinationRecipe (n := 1) (.name 40) (.const .zero) (.leaf (0, 0))))
      ((world swap).eval (.ternary .penc (.var 0) (.binary .compose (.name 40) (.name 41)) (.const .zero))) :=
  ⟨by decide, by decide,
    General.mixedCombination_not_public_nonce_constructor names swap left right (.name 40) (.const .zero)
      (.leaf (0, 0)) (.var 0) (.binary .compose (.name 40) (.name 41)) (.const .zero)
      ⟨nonce_public 40 (by omega), nonce_public 41 (by omega)⟩⟩

end ExplainableCrypto.Helios.Symbolic.MixedCiphertextSPOT
