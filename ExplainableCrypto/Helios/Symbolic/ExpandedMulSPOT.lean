import ExplainableCrypto.Helios.Symbolic.ExpandedMulTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedAddMinimumSPOT
import ExplainableCrypto.Helios.Symbolic.ExpandedMulExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedMulSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []

private theorem numeric (swap : Bool) (l r : CandidateSubstitution 1 Empty) :
    ExpandedResultsNumeric names swap l r [] :=
  accepted_expanded_results_numeric names HistoricalFrameSPOT.fixture_names_fresh l r [] (by simp) trivial swap

private theorem partial_not_cipher (swap : Bool) (l r : CandidateSubstitution 1 Empty)
    (j : Fin 2) : ¬ ((expandedFrame names swap l r []).eval (.var (expandedPartial j))).CiphertextValue := by
  rintro ⟨k,n,m,he⟩
  simp only [Frame.eval,Term.subst,expanded_frame_partial] at he
  exact penc_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ _ _ he.symm

private theorem product_not_cipher_left {a b : Ground} (h : ¬ a.CiphertextValue) :
    ¬ (Term.binary .mul a b).CiphertextValue := by
  rintro ⟨k,n,m,he⟩
  obtain ⟨_,_,_,_,ha,_,_,_⟩ := he.mul_penc_inversion
  exact h ⟨_,_,_,ha⟩

private theorem product_not_cipher_right {a b : Ground} (h : ¬ b.CiphertextValue) :
    ¬ (Term.binary .mul a b).CiphertextValue := by
  rintro ⟨k,n,m,he⟩
  obtain ⟨_,_,_,_,_,hb,_,_⟩ := he.mul_penc_inversion
  exact h ⟨_,_,_,hb⟩

private theorem three_node_product_minimum (swap : Bool) (l r : CandidateSubstitution 1 Empty)
    (a b : Recipe (ExpandedHandles 1)) (hp : (Term.binary .mul a b).Public names.restricted)
    (hc : ¬ ((expandedFrame names swap l r []).eval (.binary .mul a b)).CiphertextValue)
    (hsize : (Term.binary .mul a b).nodeCount = 3) :
    MinimalRecipe names.restricted (expandedFrame names swap l r []).value (.binary .mul a b) := by
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (expandedFrame names swap l r []).value) (.binary .mul a b) hp
  obtain ⟨u,v,rfl⟩ := expanded_minimum_non_ciphertext_mul_form names swap l r [] (numeric swap l r)
    names.restricted m hm he.symm (fun hv => hc (by obtain ⟨k,n,m,hv⟩ := hv; exact ⟨k,n,m,he.trans hv⟩))
  apply hm.of_equivalent_size hp he
  have := u.nodeCount_pos
  have := v.nodeCount_pos
  rw [hsize]
  simp only [Term.nodeCount]
  omega

/-- Every actual handle, including both publication kinds, is excluded from
multiplication values in either assignment. -/
theorem all_handles_nonmultiplication (swap : Bool) (v : Fin (ExpandedHandles 1)) (x y : Ground) :
    ¬ EqE ((world swap).eval (.var v)) (.binary .mul x y) :=
  expanded_handle_not_multiplication names swap left right [] (numeric swap left right) v x y

/-- Actual published partial/result products are global three-node minima and
cannot be fused ciphertexts. The source candidates need not be equal. -/
theorem published_product_minimum (swap : Bool) :
    let r : Recipe (ExpandedHandles 1) := .binary .mul (.var (expandedPartial 0)) (.var (expandedResult 1))
    MinimalRecipe names.restricted (world swap).value r ∧ ¬ ((world swap).eval r).CiphertextValue := by
  have hc := product_not_cipher_left (b := (world swap).eval (.var (expandedResult 1))) (partial_not_cipher swap left right 0)
  exact ⟨three_node_product_minimum swap left right _ _ ⟨trivial,trivial⟩ hc rfl,hc⟩

/-- Result zero is not a multiplicative unit, and duplicate partials do not
collapse. Source minimum size rules out both one-node aliases. -/
theorem published_multiplicity_retained (swap : Bool) :
    let p : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
    let z : Recipe (ExpandedHandles 1) := .var (expandedResult 0)
    ¬ EqE ((world swap).eval (.binary .mul p z)) ((world swap).eval p) ∧
    ¬ EqE ((world swap).eval (.binary .mul p p)) ((world swap).eval p) := by
  have close (b : Recipe (ExpandedHandles 1)) (hb : b.nodeCount = 1) (hp : b.Public names.restricted) :=
    three_node_product_minimum swap left right (.var (expandedPartial 0)) b ⟨trivial,hp⟩
      (product_not_cipher_left (partial_not_cipher swap left right 0)) (by simp only [Term.nodeCount,hb])
  constructor
  · intro he
    exact (close (.var (expandedResult 0)) rfl trivial).no_smaller (s := .var (expandedPartial 0)) trivial he (by decide)
  · intro he
    exact (close (.var (expandedPartial 0)) rfl trivial).no_smaller (s := .var (expandedPartial 0)) trivial he (by decide)

/-- The complete equality branch compares permuted published factors. A
diagonal election supplies the smaller-observation premise for this control. -/
theorem accepted_permuted_published_comparison :
    let φ := expandedFrame names false left left []
    let ψ := expandedFrame names true left left []
    let p : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
    let z : Recipe (ExpandedHandles 1) := .var (expandedResult 1)
    let r := Term.binary .mul p z
    let s := Term.binary .mul z p
    (EqE (φ.eval r) (φ.eval s) ↔ EqE (ψ.eval r) (ψ.eval s)) ∧ EqE (φ.eval r) (φ.eval s) := by
  have hc := product_not_cipher_left (b := (expandedFrame names false left left []).eval (.var (expandedResult 1))) (partial_not_cipher false left left 0)
  have hd := product_not_cipher_right (a := (expandedFrame names false left left []).eval (.var (expandedResult 1))) (partial_not_cipher false left left 0)
  have hr := three_node_product_minimum false left left (.var (expandedPartial 0)) (.var (expandedResult 1)) ⟨trivial,trivial⟩ hc rfl
  have hs := three_node_product_minimum false left left (.var (expandedResult 1)) (.var (expandedPartial 0)) ⟨trivial,trivial⟩ hd rfl
  exact ⟨accepted_expanded_minimum_non_ciphertext_multiplication_equality_swap names HistoricalFrameSPOT.fixture_names_fresh
    false true left left [] (by simp) trivial _ _ hr hs (.refl _) (.refl _) hc hd (fun _ _ _ _ _ => Iff.rfl),
    EqE.equation (.comm .mul trivial _ _)⟩

/-- A surviving product permits ciphertext fusion inside one group. The two
original occurrences become one ciphertext factor, and full-E equality is kept. -/
theorem fusion_inside_published_product (swap : Bool) :
    let a : Recipe (ExpandedHandles 1) := .ternary .penc (.name 40) (.name 41) (.const .zero)
    let b : Recipe (ExpandedHandles 1) := .ternary .penc (.name 40) (.name 42) (.const .one)
    let p : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
    let r := Term.binary .mul (.binary .mul a b) p
    let s := Term.binary .mul (combinedCiphertext (.name 40) (.name 41) (.name 42) (.const .zero) (.const .one)) p
    EqE ((world swap).eval r) ((world swap).eval s) ∧ r.mulLeaves.card = 3 ∧ s.mulLeaves.card = 2 ∧
    ¬ ((world swap).eval r).CiphertextValue :=
  ⟨EqE.binary .mul (RootStep.homomorphic _ _ _ _ _).sound (.refl _),rfl,rfl,
    product_not_cipher_right (partial_not_cipher swap left right 0)⟩

/-- Fused-product minimum representatives exercise the conditional equality
branch and its partition accounting. The original product remains non-ciphertext. -/
theorem accepted_fusion_minimum_comparison :
    let φ := expandedFrame names false left left []
    let ψ := expandedFrame names true left left []
    let a : Recipe (ExpandedHandles 1) := .ternary .penc (.name 40) (.name 41) (.const .zero)
    let b : Recipe (ExpandedHandles 1) := .ternary .penc (.name 40) (.name 42) (.const .one)
    let p : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
    let r := Term.binary .mul (.binary .mul a b) p
    let s := Term.binary .mul (combinedCiphertext (.name 40) (.name 41) (.name 42) (.const .zero) (.const .one)) p
    ∃ m k, MinimalRecipe names.restricted φ.value m ∧ MinimalRecipe names.restricted φ.value k ∧
      EqE (φ.eval m) (φ.eval r) ∧ EqE (φ.eval k) (φ.eval s) ∧
      (EqE (φ.eval m) (φ.eval k) ↔ EqE (ψ.eval m) (ψ.eval k)) ∧ EqE (ψ.eval m) (ψ.eval k) := by
  let φ := expandedFrame names false left left []
  let a : Recipe (ExpandedHandles 1) := .ternary .penc (.name 40) (.name 41) (.const .zero)
  let b : Recipe (ExpandedHandles 1) := .ternary .penc (.name 40) (.name 42) (.const .one)
  let p : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
  let r := Term.binary .mul (.binary .mul a b) p
  let s := Term.binary .mul (combinedCiphertext (.name 40) (.name 41) (.name 42) (.const .zero) (.const .one)) p
  have hp40 : 40 ∉ names.restricted := by decide
  have hp41 : 41 ∉ names.restricted := by decide
  have hp42 : 42 ∉ names.restricted := by decide
  have hrpub : r.Public names.restricted := ⟨⟨⟨hp40,hp41,trivial⟩,⟨hp40,hp42,trivial⟩⟩,trivial⟩
  have hspub : s.Public names.restricted := ⟨⟨hp40,⟨hp41,hp42⟩,trivial,trivial⟩,trivial⟩
  obtain ⟨m,hm,hem⟩ := exists_minimal_recipe (σ := φ.value) r hrpub
  obtain ⟨k,hk,hek⟩ := exists_minimal_recipe (σ := φ.value) s hspub
  have hrs : EqE (φ.eval r) (φ.eval s) := EqE.binary .mul (RootStep.homomorphic _ _ _ _ _).sound (.refl _)
  have hnc (c : Recipe (ExpandedHandles 1)) : ¬ (φ.eval (.binary .mul c p)).CiphertextValue :=
    product_not_cipher_right (partial_not_cipher false left left 0)
  have hnm : ¬ (φ.eval m).CiphertextValue := by
    rintro ⟨key,nonce,msg,hv⟩
    exact hnc _ ⟨key,nonce,msg,hem.trans hv⟩
  have hnk : ¬ (φ.eval k).CiphertextValue := by
    rintro ⟨key,nonce,msg,hv⟩
    exact hnc _ ⟨key,nonce,msg,hek.trans hv⟩
  have hi := accepted_expanded_minimum_non_ciphertext_multiplication_equality_swap names HistoricalFrameSPOT.fixture_names_fresh
    false true left left [] (by simp) trivial m k hm hk hem.symm hek.symm hnm hnk (fun _ _ _ _ _ => Iff.rfl)
  exact ⟨m,k,hm,hk,hem.symm,hek.symm,hi,hi.mp (hem.symm.trans (hrs.trans hek))⟩

/-- A projection or E5 decryption can expose a product from another raw head.
Both wrappers are nonminimum, so their raw leaves cannot justify minimum origins. -/
theorem hidden_product_wrappers (swap : Bool) :
    let p : Recipe (ExpandedHandles 1) := .binary .mul (.var (expandedPartial 0)) (.var (expandedResult 0))
    let r := Term.unary .fst (.binary .pair p (.name 50))
    let key : Recipe (ExpandedHandles 1) := .var (expandedPartial 1)
    let d := Term.binary .dec key (keyCiphertext key (.name 60) p)
    EqE ((world swap).eval r) ((world swap).eval p) ∧
    EqE ((world swap).eval d) ((world swap).eval p) ∧
    ¬ MinimalRecipe names.restricted (world swap).value r ∧
    ¬ MinimalRecipe names.restricted (world swap).value d ∧ r.mulLeaves.card = 1 ∧ p.mulLeaves.card = 2 := by
  refine ⟨.equation (.fst _ _),(RootStep.decrypt _ _ _).sound,?_,?_,rfl,rfl⟩
  · intro hm
    exact hm.raw_irreducible _ (RootStep.fst _ _).to_rewrite
  · intro hm
    exact hm.raw_irreducible _ (RootStep.decrypt _ _ _).to_rewrite

/-- An accepted E6 match stays successful and returns one, which cannot be a
multiplication value. Numeric exclusion does not turn off decryption. -/
theorem successful_E6_is_numeric (swap : Bool) :
    (∃ out, DecryptionMatch (tallyPartial names swap left right [] 1) (tallyCiphertext names swap left right [] 1) out) ∧
    EqE (tallyResult names swap left right [] 1) (.const .one) ∧
    ∀ x y, ¬ EqE (tallyResult names swap left right [] 1) (.binary .mul x y) := by
  refine ⟨(TrusteePartialSPOT.both_candidates_match swap 1).1,SharedTallySPOT.nonliteral_two_candidate_tally.2 swap,?_⟩
  intro x y he
  exact mul_not_eqE_constant _ _ .one (he.symm.trans (SharedTallySPOT.nonliteral_two_candidate_tally.2 swap))

/-- The non-ciphertext restriction matters: a fused constructor has a product
E-value without raw mul syntax. This case belongs to ciphertext equality. -/
theorem fused_ciphertext_has_product_value (swap : Bool) :
    let r : Recipe (ExpandedHandles 1) := combinedCiphertext (.name 40) (.name 41) (.name 42) (.const .zero) (.const .one)
    let a : Recipe (ExpandedHandles 1) := .ternary .penc (.name 40) (.name 41) (.const .zero)
    let b : Recipe (ExpandedHandles 1) := .ternary .penc (.name 40) (.name 42) (.const .one)
    EqE ((world swap).eval r) ((world swap).eval (.binary .mul a b)) ∧
    ((world swap).eval r).CiphertextValue ∧ ¬ (∃ a b, r = .binary .mul a b) := by
  refine ⟨(RootStep.homomorphic _ _ _ _ _).sound.symm,⟨_,_,_,.refl _⟩,?_⟩
  rintro ⟨a,b,h⟩
  cases h

end ExplainableCrypto.Helios.Symbolic.ExpandedMulSPOT
