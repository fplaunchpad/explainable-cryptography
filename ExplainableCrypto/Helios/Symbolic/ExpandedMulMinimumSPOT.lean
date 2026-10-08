import ExplainableCrypto.Helios.Symbolic.ExpandedMulMinimumClosure
import ExplainableCrypto.Helios.Symbolic.ExpandedMulMinimumExperiments
import ExplainableCrypto.Helios.Symbolic.ExpandedMulSPOT

namespace ExplainableCrypto.Helios.Symbolic.ExpandedMulMinimumSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []
abbrev reveal (r : Recipe (ExpandedHandles 1)) := Term.unary .fst (.binary .pair r (.const .bottom))

private theorem numeric (swap : Bool) (l r : CandidateSubstitution 1 Empty) : ExpandedResultsNumeric names swap l r [] :=
  accepted_expanded_results_numeric names HistoricalFrameSPOT.fixture_names_fresh l r [] (by simp) trivial swap
private theorem publicName (a : Nat) (ha : a ∉ names.restricted) : (Term.name a : Recipe (ExpandedHandles 1)).Public names.restricted := ha

private theorem product_normal {a b : Ground} (ha : Irreducible a) (hb : Irreducible b)
    (hfa : a.mulFactors = {a.baseClass}) (hfb : b.mulFactors = {b.baseClass})
    (hna : ¬ a.CiphertextValue) : Irreducible (.binary .mul a b) := by
  apply irreducible_of_normal_mul_factors
  · intro q hq
    exact (Multiset.mem_add.mp hq).elim (ha.normal_mul_factors q) (hb.normal_mul_factors q)
  · intro u hu
    obtain ⟨inputs,output,rest,h,hs,_⟩ := hu
    have hc := congrArg Multiset.card hs
    have hi := h.rank
    simp only [Term.mulFactors,hfa,hfb,Multiset.card_add,Multiset.card_singleton] at hc
    have hz : rest = 0 := Multiset.card_eq_zero.mp (by omega)
    subst rest
    have hm : a.baseClass ∈ inputs := by
      have he : inputs = {a.baseClass} + {b.baseClass} := by simpa [Term.mulFactors,hfa,hfb] using hs.symm
      rw [he]; simp
    obtain ⟨k,r,s,m,p,rfl,_⟩ := h
    simp [ciphertextPairFactors] at hm
    rcases hm with hm | hm
    · exact hna ⟨k,r,m,((baseClass_eq_iff _ _).mp hm).sound⟩
    · exact hna ⟨k,s,p,((baseClass_eq_iff _ _).mp hm).sound⟩

private theorem zero_not_cipher : ¬ (Term.const (V := Empty) .zero).CiphertextValue := by
  rintro ⟨k,r,p,he⟩
  obtain ⟨_,_,_,hh,_⟩ := he.symm.penc_irreducible_shape (constant_irreducible .zero)
  cases hh
private theorem name_not_cipher (a : Nat) : ¬ (Term.name (V := Empty) a).CiphertextValue := by
  rintro ⟨k,r,p,he⟩
  obtain ⟨_,_,_,hh,_⟩ := he.symm.penc_irreducible_shape (name_irreducible a)
  cases hh

/-- A reducible recipe using an actual result slot has a one-node shared
minimum in different-vote worlds. The supplied source recipe is not minimum. -/
theorem published_singleton_reassembly (swap : Bool) :
    let r := reveal (.var (expandedResult 1))
    ∃ m, MinimalRecipe names.restricted (world swap).value m ∧
      EqE ((world swap).eval r) ((world swap).eval m) ∧
      EqE ((world (!swap)).eval r) ((world (!swap)).eval m) ∧
      r.nodeCount = 4 ∧ m.nodeCount = 1 := by
  let slot : Recipe (ExpandedHandles 1) := .var (expandedResult 1)
  have hm : MinimalRecipe names.restricted (world swap).value slot := .of_nodeCount_one trivial rfl
  have hv : EqE ((world swap).eval (reveal slot)) (.const .one) :=
    (RootStep.fst _ _).sound.trans (SharedTallySPOT.nonliteral_two_candidate_tally.2 swap)
  let p := MultiplicationPartition.single (reveal slot) (.const .one)
    (σ := (world swap).value) (restricted := names.restricted) ⟨trivial,trivial⟩ hv rfl
  have hshared := expanded_sharedMinimum_of_partition_shared_pieces names swap left right [] (numeric swap left right)
    (world (!swap)) _ p (constant_irreducible .one) (by
      intro x hx
      have he := Multiset.mem_singleton.mp hx
      subst x
      exact .of_recipe_eqE hm (RootStep.fst _ _).sound)
  obtain ⟨m,hmin,he,he'⟩ := hshared
  have hb := hmin.least slot trivial (he.symm.trans (RootStep.fst _ _).sound)
  have hp := m.nodeCount_pos
  exact ⟨m,hmin,he,he',rfl,by change m.nodeCount ≤ 1 at hb; omega⟩

/-- Two wrapped zero-result occurrences shrink from nine to three nodes,
retaining both multiplication factors; zero is not a multiplicative unit. -/
theorem duplicate_results_reassemble (swap : Bool) :
    let slot : Recipe (ExpandedHandles 1) := .var (expandedResult 0)
    let r := Term.binary .mul (reveal slot) (reveal slot)
    ∃ m, MinimalRecipe names.restricted (world swap).value m ∧
      EqE ((world swap).eval r) ((world swap).eval m) ∧
      EqE ((world (!swap)).eval r) ((world (!swap)).eval m) ∧
      r.nodeCount = 9 ∧ m.nodeCount = 3 ∧ ¬ EqE ((world swap).eval m) ((world swap).eval slot) := by
  let slot : Recipe (ExpandedHandles 1) := .var (expandedResult 0)
  have hm : MinimalRecipe names.restricted (world swap).value slot := .of_nodeCount_one trivial rfl
  have hz := SharedTallySPOT.nonliteral_two_candidate_tally.1 swap
  have hv : EqE ((world swap).eval (reveal slot)) (.const .zero) := (RootStep.fst _ _).sound.trans hz
  let p0 := MultiplicationPartition.single (reveal slot) (.const .zero)
    (σ := (world swap).value) (restricted := names.restricted) ⟨trivial,trivial⟩ hv rfl
  let p := p0.mul p0
  have hn := product_normal (constant_irreducible .zero) (constant_irreducible .zero) rfl rfl zero_not_cipher
  have hs := expanded_sharedMinimum_of_partition_shared_pieces names swap left right [] (numeric swap left right)
    (world (!swap)) _ p hn (by
      intro x hx
      simp only [p,p0,MultiplicationPartition.mul,MultiplicationPartition.single,
        Multiset.mem_add,Multiset.mem_singleton,or_self] at hx
      subst x
      exact .of_recipe_eqE hm (RootStep.fst _ _).sound)
  obtain ⟨m,hmin,he,he'⟩ := hs
  have hmprod := expanded_minimum_mul_of_normal_groups names swap left right [] (numeric swap left right)
    names.restricted slot slot hm hm hz hz rfl rfl hn
  have heq : EqE ((world swap).eval m) ((world swap).eval (.binary .mul slot slot)) :=
    he.symm.trans (.binary .mul (RootStep.fst _ _).sound (RootStep.fst _ _).sound)
  have hlo := hmprod.least m hmin.isPublic heq.symm
  have hhi := hmin.least (.binary .mul slot slot) ⟨trivial,trivial⟩ heq
  have hsize : m.nodeCount = 3 := by change 3 ≤ m.nodeCount at hlo; change m.nodeCount ≤ 3 at hhi; omega
  exact ⟨m,hmin,he,he',rfl,hsize,fun bad => hmin.no_smaller (s := slot) trivial bad (by rw [hsize]; decide)⟩

/-- Minimum children using both new publication kinds supply an actual normal
partition. Whole-product minimality is not a premise of partition existence. -/
theorem published_children_partition (swap : Bool) :
    let r : Recipe (ExpandedHandles 1) := .binary .mul (.var (expandedPartial 0)) (.var (expandedResult 1))
    ∃ t, Irreducible t ∧ Nonempty (MultiplicationPartition names.restricted (world swap).value r t) := by
  apply expanded_normal_partition_of_minimum_mul_leaves names swap left right [] (numeric swap left right)
    names.restricted (.binary .mul (.var (expandedPartial 0)) (.var (expandedResult 1))) ⟨trivial,trivial⟩
  intro a ha
  simp only [Term.mulLeaves,Multiset.mem_add,Multiset.mem_singleton] at ha
  rcases ha with rfl | rfl <;> exact .of_nodeCount_one trivial rfl

abbrev first : Recipe (ExpandedHandles 1) := .ternary .penc (.name 40) (.name 41) (.const .zero)
abbrev second : Recipe (ExpandedHandles 1) := .ternary .penc (.name 40) (.name 42) (.const .one)
abbrev fused : Recipe (ExpandedHandles 1) := .ternary .penc (.name 40)
  (.binary .compose (.name 41) (.name 42)) (.const .one)

private theorem literal_cipher_minimum (swap : Bool) (l r : CandidateSubstitution 1 Empty)
    (nonce : Nat) (bit : Constant) (hp : nonce ∉ names.restricted) :
    MinimalRecipe names.restricted (expandedFrame names swap l r []).value
      (.ternary .penc (.name 40) (.name nonce) (.const bit)) := by
  have hr : (Term.ternary .penc (.name 40) (.name nonce) (.const bit) : Recipe (ExpandedHandles 1)).Public names.restricted :=
    ⟨publicName 40 (by decide),hp,trivial⟩
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (expandedFrame names swap l r []).value) _ hr
  apply hm.of_equivalent_size hr he
  have hs := expanded_minimum_ciphertext_syntax names swap l r [] (numeric swap l r) names.restricted m hm he.symm
  cases hs with
  | constructed k u p =>
    have := k.nodeCount_pos
    have := u.nodeCount_pos
    have := p.nodeCount_pos
    simp only [Term.nodeCount]
    omega
  | selected v hc =>
    obtain ⟨i,j,_,_,hv⟩ := expanded_projection_ciphertext_origin names swap l r [] (numeric swap l r) v hc he.symm
    have hk := ((EqE.penc_iff _ _ _ _ _ _).mp hv).1
    obtain ⟨_,hh,_⟩ := hk.pk_irreducible_shape (name_irreducible 40)
    cases hh
  | mul ha hb =>
    obtain ⟨_,_,_,_,hva,hvb,_,_⟩ := he.symm.mul_penc_inversion
    have hsa := ciphertext_recipe_size_ge_two (expandedFrame names swap l r []).value _ _ _
      (fun v => expanded_handle_not_ciphertext names swap l r [] (numeric swap l r) v _ _ _) hva
    have hsb := ciphertext_recipe_size_ge_two (expandedFrame names swap l r []).value _ _ _
      (fun v => expanded_handle_not_ciphertext names swap l r [] (numeric swap l r) v _ _ _) hvb
    simp only [Term.nodeCount]
    omega

/-- Normal partition endpoints matter: two globally minimum constructed
ciphertexts still fuse to a smaller recipe. -/
theorem minimum_ciphertexts_can_fuse (swap : Bool) :
    MinimalRecipe names.restricted (world swap).value first ∧
    MinimalRecipe names.restricted (world swap).value second ∧
    EqE (Term.binary .mul first second) fused ∧
    (Term.binary .mul first second).nodeCount = 9 ∧ fused.nodeCount = 6 ∧
    ¬ Irreducible ((world swap).eval (.binary .mul first second)) := by
  refine ⟨literal_cipher_minimum swap left right 41 .zero (by decide),
    literal_cipher_minimum swap left right 42 .one (by decide),?_,rfl,rfl,?_⟩
  · exact (RootStep.homomorphic _ _ _ _ _).sound.trans
      (.ternary .penc (.refl _) (.refl _) (.equation .zero_one))
  · intro hn
    exact hn _ (RootStep.homomorphic _ _ _ _ _).to_modulo

/-- The full local theorem genuinely minimizes: minimum children have sizes
four and six, but their eleven-node non-ciphertext product has a shared minimum
of at most eight nodes. Diagonal candidates inhabit the smaller-minimum premise. -/
theorem minimum_children_product_shrinks :
    let φ := expandedFrame names false left left []
    let ψ := expandedFrame names true left left []
    let b := Term.binary .mul (.name 40) second
    let r := Term.binary .mul first b
    MinimalRecipe names.restricted φ.value first ∧ MinimalRecipe names.restricted φ.value b ∧
    ¬ (φ.eval r).CiphertextValue ∧
    ∃ m, MinimalRecipe names.restricted φ.value m ∧ EqE (φ.eval r) (φ.eval m) ∧
      EqE (ψ.eval r) (ψ.eval m) ∧ r.nodeCount = 11 ∧ m.nodeCount ≤ 8 ∧ m.nodeCount < r.nodeCount := by
  dsimp only
  let φ := expandedFrame names false left left []
  let ψ := expandedFrame names true left left []
  have hf := literal_cipher_minimum false left left 41 .zero (by decide)
  have hs := literal_cipher_minimum false left left 42 .one (by decide)
  have hn40 : MinimalRecipe names.restricted φ.value (.name 40) := .of_nodeCount_one (publicName 40 (by decide)) rfl
  have hnormal := product_normal (name_irreducible 40)
    ((name_irreducible 40).penc (name_irreducible 42) (constant_irreducible .one)) rfl rfl (name_not_cipher 40)
  have hb := expanded_minimum_mul_of_normal_groups names false left left [] (numeric false left left) names.restricted
    (.name 40) second hn40 hs (.refl _) (.refl _) rfl rfl hnormal
  have hnot : ¬ (φ.eval (.binary .mul first (.binary .mul (.name 40) second))).CiphertextValue := by
    rintro ⟨k,r,p,he⟩
    obtain ⟨_,_,_,_,_,he',_,_⟩ := he.mul_penc_inversion
    obtain ⟨_,_,_,_,he'',_,_,_⟩ := he'.mul_penc_inversion
    exact name_not_cipher 40 ⟨_,_,_,he''⟩
  have hsmall : Frame.SharedMinimaBelow φ ψ (Term.binary .mul first (.binary .mul (.name 40) second)).nodeCount := by
    intro r hp _
    obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := φ.value) r hp
    exact ⟨m,hm,he,he⟩
  obtain ⟨m,hm,he,he'⟩ := accepted_expanded_minimum_children_non_ciphertext_mul_shared names
    HistoricalFrameSPOT.fixture_names_fresh false true left left [] (by simp) trivial first
    (.binary .mul (.name 40) second) hf hb hnot hsmall
  have hraw : EqE (.binary .mul first (.binary .mul (.name 40) second)) (.binary .mul fused (.name 40)) :=
    (EqE.binary .mul (.refl _) (.equation (.comm .mul trivial _ _))).trans
      ((EqE.equation (.assoc .mul trivial _ _ _)).symm.trans
        (.binary .mul (minimum_ciphertexts_can_fuse false).2.2.1 (.refl _)))
  have hp : (Term.binary .mul fused (.name 40)).Public names.restricted := by
    change ((40 ∉ names.restricted) ∧ ((41 ∉ names.restricted) ∧ (42 ∉ names.restricted)) ∧ True) ∧ (40 ∉ names.restricted)
    decide
  have hle := hm.least (.binary .mul fused (.name 40)) hp (he.symm.trans (hraw.subst φ.value))
  have hsize : m.nodeCount ≤ 8 := hle
  exact ⟨hf,hb,hnot,m,hm,he,he',rfl,hsize,by change m.nodeCount < 11; omega⟩

/-- Matching only the source does not justify a shared replacement; the same
public handle/name test distinguishes these two concrete frames. -/
theorem source_only_replacement_fails :
    let φ : Frame ∅ 1 := ⟨fun _ => .name 40⟩
    let ψ : Frame ∅ 1 := ⟨fun _ => .name 41⟩
    EqE (φ.eval (.var 0)) (φ.eval (.name 40)) ∧ ¬ EqE (ψ.eval (.var 0)) (ψ.eval (.name 40)) := by
  exact ⟨.refl _,fun he => (by decide : 41 ≠ 40) ((EqE.name_iff 41 40).mp he)⟩

/-- Actual non-ciphertext partitions have at least two pieces, and every
piece retains publicness and a strict bound against the original product. -/
theorem published_partition_piece_bounds (swap : Bool) :
    let r : Recipe (ExpandedHandles 1) := .binary .mul (.var (expandedPartial 0)) (.var (expandedResult 1))
    ∃ x y, Irreducible (.binary .mul x y) ∧
      ∃ p : MultiplicationPartition names.restricted (world swap).value r (.binary .mul x y),
        2 ≤ p.pieces.card ∧ ∀ z ∈ p.pieces, z.1.Public names.restricted ∧ z.1.nodeCount < r.nodeCount := by
  obtain ⟨t,ht,⟨p⟩⟩ := published_children_partition swap
  rcases p.value.mul_irreducible_shape ht with ⟨x,y,rfl⟩ | ⟨k,nr,m,rfl⟩
  · refine ⟨x,y,ht,p,?_,fun z hz => p.normal_product_pieces_smaller rfl z hz⟩
    have hc := congrArg Multiset.card p.targetFactors
    have hx := Multiset.card_pos.mpr x.mulFactors_nonempty
    have hy := Multiset.card_pos.mpr y.mulFactors_nonempty
    simp only [Term.mulFactors,Multiset.card_add,Multiset.card_map] at hc
    omega
  · exact False.elim ((ExpandedMulSPOT.published_product_minimum swap).2 ⟨k,nr,m,p.value⟩)

/-- A nonminimum raw leaf can hide a whole product. This blocks dropping the
minimum-leaf premise from source normal partition construction. -/
theorem hidden_product_needs_minimum_leaf (swap : Bool) :
    let p : Recipe (ExpandedHandles 1) := .binary .mul (.var (expandedPartial 0)) (.var (expandedResult 0))
    let r := Term.unary .fst (.binary .pair p (.name 50))
    EqE ((world swap).eval r) ((world swap).eval p) ∧
      ¬ MinimalRecipe names.restricted (world swap).value r ∧ r.mulLeaves.card = 1 ∧ p.mulLeaves.card = 2 :=
  ⟨(ExpandedMulSPOT.hidden_product_wrappers swap).1,
    (ExpandedMulSPOT.hidden_product_wrappers swap).2.2.1,
    (ExpandedMulSPOT.hidden_product_wrappers swap).2.2.2.2⟩

end ExplainableCrypto.Helios.Symbolic.ExpandedMulMinimumSPOT
