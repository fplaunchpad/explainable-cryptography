import ExplainableCrypto.Helios.Symbolic.MultiplicationObservationInduction
import ExplainableCrypto.Helios.Symbolic.AdditionObservationSPOT

namespace ExplainableCrypto.Helios.Symbolic.MultiplicationObservationSPOT
open Historical General
abbrev names := ProofObservationSPOT.names
abbrev left := ProofObservationSPOT.left
abbrev right := ProofObservationSPOT.right
abbrev world := ProofObservationSPOT.world
abbrev reveal := StuckDestructorSPOT.reveal
abbrev multiplied (x y : Nat) : Recipe 3 := .binary .mul (.name x) (.name y)
abbrev first : Ground := .ternary .penc (.name 40) (.name 41) (.const .zero)
abbrev second : Ground := .ternary .penc (.name 40) (.name 42) (.const .one)
abbrev combined : Ground := combinedCiphertext (.name 40) (.name 41) (.name 42) (.const .zero) (.const .one)
abbrev source : Ground := .binary .mul (.binary .mul first second) (.name 50)
abbrev target : Ground := .binary .mul combined (.name 50)

private theorem with_name_normal (t : Ground) (ht : Irreducible t)
    (hf : t.mulFactors = {t.baseClass}) (n : Nat) : Irreducible (.binary .mul t (.name n)) := by
  apply irreducible_of_normal_mul_factors
  · intro q hq
    rcases Multiset.mem_add.mp hq with hq | hq
    · exact ht.normal_mul_factors q hq
    · exact (name_irreducible n).normal_mul_factors q hq
  · intro u hu
    obtain ⟨inputs, output, rest, h, hs, _⟩ := hu
    have hc := congrArg Multiset.card hs
    have hi := h.rank
    simp only [Term.mulFactors, hf, Multiset.card_add, Multiset.card_singleton] at hc
    have hz : rest = 0 := Multiset.card_eq_zero.mp (by omega)
    subst rest
    have hn : (Term.name (V := Empty) n).baseClass ∈ inputs := by
      have he : inputs = t.mulFactors + {(.name n : Ground).baseClass} := by simpa [Term.mulFactors] using hs.symm
      rw [he]; simp
    obtain ⟨k, r, s, m, p, rfl, _⟩ := h
    simp [ciphertextPairFactors] at hn
    rcases hn with hn | hn <;> have bad := ((baseClass_eq_iff _ _).mp hn).head_eq <;> cases bad

private theorem names_normal (a b : Nat) : Irreducible (.binary .mul (.name a) (.name b) : Ground) :=
  with_name_normal _ (name_irreducible a) rfl b
private theorem first_normal : Irreducible first :=
  (name_irreducible 40).penc (name_irreducible 41) (constant_irreducible .zero)
private theorem second_normal : Irreducible second :=
  (name_irreducible 40).penc (name_irreducible 42) (constant_irreducible .one)
private theorem combined_normal : Irreducible combined :=
  (name_irreducible 40).penc ((name_irreducible 41).compose (name_irreducible 42))
    ((constant_irreducible .zero).add (constant_irreducible .one))
private theorem source_factors : source.NormalMulFactors := by
  intro q hq
  simp only [Term.mulFactors, Multiset.mem_add, Multiset.mem_singleton] at hq
  rcases hq with (rfl | rfl) | rfl
  · exact ⟨first, rfl, first_normal⟩
  · exact ⟨second, rfl, second_normal⟩
  · exact ⟨.name 50, rfl, name_irreducible 50⟩
private theorem fusion_step : OuterFusion source target :=
  OuterFusion.of_factors _ _ _ _ _ _ _ {(.name 50 : Ground).baseClass} (by simp [Term.mulFactors, ciphertextPairFactors]) rfl

/-- Input zero from the unfused-bag gate: equality holds after fusing two normal
ciphertexts, while the whole product remains non-ciphertext and the bag shrinks. -/
theorem fusion_is_required :
    source.NormalMulFactors ∧ EqE source target ∧ source.mulFactors ≠ target.mulFactors ∧
    ¬ source.CiphertextValue ∧ Irreducible target := by
  have ht := with_name_normal combined combined_normal rfl 50
  have he := fusion_step.to_modulo.sound
  refine ⟨source_factors, he, ?_, ?_, ht⟩
  · intro h
    have hc := congrArg Multiset.card h
    simp [combined, combinedCiphertext, Term.mulFactors] at hc
  · rintro ⟨k, r, m, h⟩
    exact ht.mul_not_ciphertext ⟨k, r, m, he.symm.trans h⟩

/-- The general equality characterization joins by fusion rather than demanding
literal equality of factor bags. The normal endpoint has no internal step. -/
theorem normal_fusion_join_instance :
    ∃ bag, Relation.ReflTransGen (BagFusion CipherFusion) source.mulFactors bag ∧
      Relation.ReflTransGen (BagFusion CipherFusion) target.mulFactors bag :=
  (eqE_iff_normal_fusion_join _ _ source_factors fusion_is_required.2.2.2.2.normal_mul_factors).mp fusion_is_required.2.1

/-- Two same-name factors remain two occurrences and cannot become a name or
ciphertext. Normal factor accounting does not make multiplication idempotent. -/
theorem duplicates_are_observable :
    ¬ EqE (.binary .mul (.name 40) (.name 40) : Ground) (.name 40) ∧
    ¬ (Term.binary .mul (.name 40) (.name 40) : Ground).CiphertextValue :=
  ⟨mul_not_eqE_name _ _ 40, (names_normal 40 40).mul_not_ciphertext⟩

/-- Input zero from the hidden-product gate: one raw leaf exposes a proper
product, and fails the required normal-factor premise. -/
theorem hidden_product_needs_normalization :
    EqE (reveal (.binary .mul (.name 40) (.name 41))) (.binary .mul (.name 40) (.name 41)) ∧
    ¬ (reveal (.binary .mul (.name 40) (.name 41))).NormalMulFactors := by
  refine ⟨(RootStep.fst _ _).sound, ?_⟩
  intro h
  have hn : Irreducible (reveal (.binary .mul (.name 40) (.name 41))) :=
    (h _ (by simp [reveal, StuckDestructorSPOT.reveal, Term.mulFactors])).irreducible
  exact hn _ (RootStep.fst _ _).to_modulo

/-- Different public keys cannot fuse to any ciphertext, even under full E. -/
theorem wrong_key_rejected :
    ¬ (Term.binary .mul first (.ternary .penc (.name 43) (.name 42) (.const .one)) : Ground).CiphertextValue := by
  rintro ⟨k, r, m, he⟩
  obtain ⟨_, _, _, _, ha, hb, _, _⟩ := he.mul_penc_inversion
  have hk := ((EqE.penc_iff _ _ _ _ _ _).mp ha).1.trans ((EqE.penc_iff _ _ _ _ _ _).mp hb).1.symm
  have h := (EqE.name_iff 40 43).mp hk
  omega

/-- A concrete three-piece public partition loses exactly one piece under
fusion, preserving the source factor bag and strict final-group recipe budgets. -/
theorem fusion_partition_budget :
    ∃ p : MultiplicationPartition ∅ (Term.var : Empty → Ground) source target,
      p.pieces.card = 2 ∧ ∀ q ∈ p.pieces, q.1.Public ∅ ∧ q.1.nodeCount < source.nodeCount := by
  let p : MultiplicationPartition ∅ (Term.var : Empty → Ground) source source := {
    pieces := (first,first) ::ₘ (second,second) ::ₘ {(.name 50,.name 50)}
    sourceFactors := by
      simp only [Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons, Multiset.sum_singleton, Term.mulFactors]
      ac_rfl
    targetFactors := by simp [Term.mulFactors]
    values := by
      intro q hq
      rw [Term.subst_var]
      simp only [Multiset.mem_cons, Multiset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl <;> exact .refl _
    publicPieces := by
      intro q hq
      simp only [Multiset.mem_cons, Multiset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl <;> simp [Term.Public]
    budget := by decide
    value := by rw [Term.subst_var]; exact .refl _
  }
  obtain ⟨q⟩ := p.fusion fusion_step
  refine ⟨q, ?_, fun x hx => q.normal_product_pieces_smaller rfl x hx⟩
  have hc := congrArg Multiset.card q.targetFactors
  simpa [Term.mulFactors] using hc

/-- Normal literal name products attain the exact three-node minimum for all
valid candidate assignments and both swaps, including repeated factors. -/
theorem literal_mul_minimum (swap : Bool) (a b : CandidateSubstitution 1 Empty)
    (x y : Nat) (hx : x ∉ names.restricted) (hy : y ∉ names.restricted) :
    MinimalRecipe names.restricted (General.frame names swap a b).value (multiplied x y) := by
  have hp : (multiplied x y).Public names.restricted := ⟨hx, hy⟩
  obtain ⟨r, hr, he⟩ := exists_minimal_recipe (σ := (General.frame names swap a b).value) _ hp
  obtain ⟨u, v, rfl⟩ := minimum_normal_mul_form names swap a b names.restricted r hr (names_normal x y) he.symm
  refine ⟨hp, fun s hs hes => ?_⟩
  have hle := hr.least s hs (he.symm.trans hes)
  have := u.nodeCount_pos
  have := v.nodeCount_pos
  simp only [Term.nodeCount] at hle ⊢
  omega

/-- Distinct permuted minima instantiate the complete branch with a reducible
supplied target. The six-node bounded premise is inhabited in diagonal worlds. -/
theorem permuted_minimum_step :
    (multiplied 40 41) ≠ (multiplied 41 40) ∧
    EqE ((General.frame names true left left).eval (multiplied 40 41))
      ((General.frame names true left left).eval (multiplied 41 40)) := by
  have hr := literal_mul_minimum false left left 40 41 (by decide) (by decide)
  have hs := literal_mul_minimum false left left 41 40 (by decide) (by decide)
  have he : EqE ((General.frame names false left left).eval (multiplied 40 41))
      (.binary .mul (reveal (.name 40)) (.name 41)) :=
    .binary .mul (RootStep.fst _ _).sound.symm (.refl _)
  exact ⟨by decide, (minimum_non_ciphertext_multiplication_equality_swap names left left _ _ hr hs he (.refl _)
    (names_normal 40 41).mul_not_ciphertext (names_normal 41 40).mul_not_ciphertext
    (CiphertextObservationSPOT.diagonal_observations _)).mp (.equation (.comm .mul trivial _ _))⟩

/-- Unequal multiplicities remain unequal through the complete minimum branch. -/
theorem unequal_minimum_step :
    ¬ EqE ((General.frame names false left left).eval (multiplied 40 41))
      ((General.frame names false left left).eval (multiplied 40 40)) ∧
    (EqE ((General.frame names false left left).eval (multiplied 40 41))
        ((General.frame names false left left).eval (multiplied 40 40)) ↔
      EqE ((General.frame names true left left).eval (multiplied 40 41))
        ((General.frame names true left left).eval (multiplied 40 40))) := by
  have hr := literal_mul_minimum false left left 40 41 (by decide) (by decide)
  have hs := literal_mul_minimum false left left 40 40 (by decide) (by decide)
  refine ⟨?_, minimum_non_ciphertext_multiplication_equality_swap names left left _ _ hr hs (.refl _) (.refl _)
    (names_normal 40 41).mul_not_ciphertext (names_normal 40 40).mul_not_ciphertext
    (CiphertextObservationSPOT.diagonal_observations _)⟩
  intro he
  have hbag := ((irreducible_eqE_iff_base (names_normal 40 41) (names_normal 40 40)).mp he).mul_factors
  have hc := Multiset.singleton_inj.mp (add_left_cancel hbag)
  have hn := (BaseEq.name_iff 41 40).mp ((baseClass_eq_iff _ _).mp hc)
  omega

/-- A public wrapper has a non-ciphertext product value with a different raw
head, demonstrating why exact origins require minimum size. -/
theorem origin_needs_minimum (swap : Bool) :
    let r : Recipe 3 := .unary .fst (.binary .pair (multiplied 40 41) (.const .bottom))
    r.Public names.restricted ∧ EqE ((world swap).eval r) ((world swap).eval (multiplied 40 41)) ∧
      ¬ MinimalRecipe names.restricted (world swap).value r := by
  have hp : (multiplied 40 41).Public names.restricted := by change 40 ∉ names.restricted ∧ 41 ∉ names.restricted; decide
  have he : EqE ((world swap).eval (.unary .fst (.binary .pair (multiplied 40 41) (.const .bottom))))
      ((world swap).eval (multiplied 40 41)) := (RootStep.fst _ _).sound
  exact ⟨⟨hp, trivial⟩, he, fun hm => hm.no_smaller hp he (by decide)⟩

/-- Fusion cannot discard an unrelated public factor. The source remains a
non-ciphertext product rather than collapsing to the combined ciphertext alone. -/
theorem fusion_retains_remainder : ¬ EqE source combined := by
  intro he
  exact fusion_is_required.2.2.2.1 ⟨.name 40, .binary .compose (.name 41) (.name 42),
    .binary .add (.const .zero) (.const .one), he⟩

/-- Zero is an ordinary multiplication factor, not the auxiliary fold identity. -/
theorem zero_is_no_unit : ¬ EqE (.binary .mul (.const .zero) (.name 40) : Ground) (.name 40) :=
  mul_not_eqE_name _ _ 40

end ExplainableCrypto.Helios.Symbolic.MultiplicationObservationSPOT
