import ExplainableCrypto.Helios.Symbolic.HistoricalMinimumDestructors
import ExplainableCrypto.Helios.Symbolic.HistoricalCiphertextForms
import ExplainableCrypto.Helios.Symbolic.HistoricalMinimumProofs
import ExplainableCrypto.Helios.Symbolic.ProjectionChainSPOT
import ExplainableCrypto.Helios.Symbolic.CiphertextProductSPOT

namespace ExplainableCrypto.Helios.Symbolic.MinimumOriginSPOT
open Historical

abbrev ns := HistoricalFrameSPOT.names
abbrev σ : Fin 3 → Ground := (frame ns false 0 1).value
abbrev key : Ground := .unary .pk (.name 10)
abbrev second : Recipe 3 := (Term.var 1).project 1
abbrev target : Ground := .ternary .penc key (.name 21) (.const .zero)

/-- A known three-node minimum gets a certificate, public smaller plaintext,
and exact target components without supplying any origin certificate. -/
theorem minimum_selector_reconstruction :
    ∃ p s, CiphertextProduct σ key second p s ∧ p.Public ns.nonceNames ∧
      p.nodeCount < second.nodeCount ∧ EqE s (.name 21) ∧ EqE (p.subst σ) (.const .zero) :=
  minimum_ciphertext_certificate ns false 0 1 ns.nonceNames second
    (HistoricalSelectorSPOT.second_minimal _) HistoricalSelectorSPOT.second_evaluation

theorem minimum_selector_exact_form : CiphertextRecipeForm 1 second :=
  minimum_ciphertext_form ns false 0 1 ns.nonceNames second
    (HistoricalSelectorSPOT.second_minimal _) HistoricalSelectorSPOT.second_evaluation

abbrev stuckRecipe : Recipe 3 := .binary .dec (.name 40) (.name 41)
abbrev stuck : Ground := .binary .dec (.name 40) (.name 41)

theorem stuck_irreducible : Irreducible stuck := by
  intro t hs
  rcases hs.rigid_binary_cases (by simp [AC]) with hr | ⟨a, ha, _⟩ | ⟨b, hb, _⟩
  · rcases hr.decryption_cases with ⟨_, _, _, _, hb, _⟩ | ⟨_, _, _, _, hb, _⟩ <;> cases hb.head_eq
  · exact name_irreducible 40 a ha
  · exact name_irreducible 41 b hb

private theorem atom_not_stuck (a : Ground) (ha : Irreducible a)
    (hh : a.headTag ≠ .binary .dec) : ¬ EqE a stuck := by
  intro he
  exact hh ((irreducible_eqE_iff_base ha stuck_irreducible).mp he).head_eq

private theorem pair_not_stuck (a b : Ground) : ¬ EqE (.binary .pair a b) stuck := by
  intro he
  cases stuck_irreducible.pair_head_of_eq he.symm

private theorem pk_not_stuck (a : Ground) : ¬ EqE (.unary .pk a) stuck := by
  intro he
  obtain ⟨_, hh, _⟩ := he.pk_irreducible_shape stuck_irreducible
  cases hh

private theorem penc_not_stuck (k r m : Ground) : ¬ EqE (.ternary .penc k r m) stuck := by
  intro he
  obtain ⟨_, _, _, hh, _⟩ := he.penc_irreducible_shape stuck_irreducible
  cases hh

private theorem unary_nonpair_not_stuck (f : Unary) (a : Ground)
    (hp : ∀ x y, ¬ EqE a (.binary .pair x y)) : ¬ EqE (.unary f a) stuck := by
  intro he
  cases f with
  | pk => exact pk_not_stuck _ he
  | fst =>
    obtain ⟨_, hh, _⟩ := projection_normal_shape_of_no_pair .fst (Or.inl rfl) a hp stuck_irreducible he
    cases hh
  | snd =>
    obtain ⟨_, hh, _⟩ := projection_normal_shape_of_no_pair .snd (Or.inr rfl) a hp stuck_irreducible he
    cases hh

private theorem handles_not_stuck (v : Fin 3) : ¬ EqE (σ v) stuck := by
  fin_cases v
  · exact pk_not_stuck _
  · exact pair_not_stuck _ _
  · exact pair_not_stuck _ _

private theorem unary_handles_not_stuck (f : Unary) (v : Fin 3) : ¬ EqE (.unary f (σ v)) stuck := by
  cases f with
  | pk => exact pk_not_stuck _
  | fst =>
    fin_cases v
    · exact unary_nonpair_not_stuck .fst _ (fun _ _ => pk_not_eqE_pair _ _ _)
    · intro he
      exact penc_not_stuck _ _ _
        ((RootStep.fst HistoricalSelectorSPOT.first0 HistoricalSelectorSPOT.tail0).sound.symm.trans he)
    · intro he
      exact penc_not_stuck _ _ _
        ((RootStep.fst HistoricalSelectorSPOT.first1 HistoricalSelectorSPOT.tail1).sound.symm.trans he)
  | snd =>
    fin_cases v
    · exact unary_nonpair_not_stuck .snd _ (fun _ _ => pk_not_eqE_pair _ _ _)
    · intro he
      exact pair_not_stuck _ _
        ((RootStep.snd HistoricalSelectorSPOT.first0 HistoricalSelectorSPOT.tail0).sound.symm.trans he)
    · intro he
      exact pair_not_stuck _ _
        ((RootStep.snd HistoricalSelectorSPOT.first1 HistoricalSelectorSPOT.tail1).sound.symm.trans he)

private theorem short_recipe_not_stuck (r : Recipe 3) (hr : r.nodeCount ≤ 2) :
    ¬ EqE (r.subst σ) stuck := by
  rcases r.nodeCount_two_cases hr with hs | ⟨f, a, rfl, ha⟩
  · rcases r.nodeCount_one_cases hs with ⟨n, rfl⟩ | ⟨v, rfl⟩ | ⟨c, rfl⟩
    · exact atom_not_stuck _ (name_irreducible n) (by simp [Term.subst, Term.headTag])
    · exact handles_not_stuck v
    · exact atom_not_stuck _ (constant_irreducible c) (by cases c <;> simp [Term.subst, Term.headTag])
  · rcases a.nodeCount_one_cases ha with ⟨n, rfl⟩ | ⟨v, rfl⟩ | ⟨c, rfl⟩
    · apply unary_nonpair_not_stuck f
      intro x y he
      cases (name_irreducible n).pair_head_of_eq he
    · exact unary_handles_not_stuck f v
    · apply unary_nonpair_not_stuck f
      intro x y he
      have hh := (constant_irreducible c).pair_head_of_eq he
      cases c <;> cases hh

/-- The actual historical frame admits a three-node minimum decrypt.
The lower bound excludes every size-one/two recipe, including all names. -/
theorem stuck_minimum : MinimalRecipe ns.nonceNames σ stuckRecipe := by
  refine ⟨by change 40 ∉ ns.nonceNames ∧ 41 ∉ ns.nonceNames; decide, ?_⟩
  intro r _ he
  change 3 ≤ r.nodeCount
  by_contra hn
  exact short_recipe_not_stuck r (by omega) he.symm

theorem minimum_decryption_control :
    MinimalRecipe ns.nonceNames σ stuckRecipe ∧ Irreducible stuck ∧
    BaseEq stuck (.binary .dec (.name 40) (.name 41)) ∧
    (∀ out, ¬ DecryptionMatch (Term.name (V := Empty) 40) (.name 41) out) :=
  ⟨stuck_minimum, stuck_irreducible,
    minimum_decryption_normal_form ns false 0 1 ns.nonceNames _ _ stuck_minimum
      (name_irreducible 40) (name_irreducible 41) stuck_irreducible (.refl _) (.refl _) (.refl _),
    minimum_decryption_no_match ns false 0 1 ns.nonceNames _ _ stuck_minimum⟩

abbrev projectedName : Recipe 3 := .unary .fst (.name 40)
abbrev projectedNameValue : Ground := .unary .fst (.name 40)

theorem projected_name_irreducible : Irreducible projectedNameValue := by
  intro t hs
  rcases hs.unary_cases with hr | ⟨a, ha, _⟩
  · rcases hr.unary_projection_cases with ⟨_, _, _, hp, _⟩ | ⟨_, _, _, hp, _⟩ <;> cases hp.head_eq
  · exact name_irreducible 40 a ha

theorem projected_name_minimum : MinimalRecipe ns.nonceNames σ projectedName := by
  refine ⟨by change 40 ∉ ns.nonceNames; decide, ?_⟩
  intro r _ he
  change 2 ≤ r.nodeCount
  by_contra hn
  rcases r.nodeCount_one_cases (by omega) with ⟨n, rfl⟩ | ⟨v, rfl⟩ | ⟨c, rfl⟩
  · have hh := ((irreducible_eqE_iff_base projected_name_irreducible (name_irreducible n)).mp he).head_eq
    cases hh
  · fin_cases v
    · obtain ⟨_, hh, _⟩ := he.symm.pk_irreducible_shape projected_name_irreducible
      cases hh
    · cases projected_name_irreducible.pair_head_of_eq he
    · cases projected_name_irreducible.pair_head_of_eq he
  · have hh := ((irreducible_eqE_iff_base projected_name_irreducible (constant_irreducible c)).mp he).head_eq
    cases c <;> cases hh

theorem minimum_projection_retains_head : BaseEq projectedNameValue (.unary .fst (.name 40)) := by
  rcases minimum_projection_normal_form ns false 0 1 ns.nonceNames .fst (Or.inl rfl)
    (.name 40) projected_name_minimum (name_irreducible 40) projected_name_irreducible
    (.refl _) (.refl _) with ⟨i, j, _, he⟩ | he
  · cases j with
    | zero => cases he
    | succ j => rw [Term.drop_succ_outer] at he; cases he
  · exact he

/-- The minimum second-field control forces the bounded honest-tail exception. -/
theorem minimum_projection_exception_required :
    ∃ a' : Ground, Irreducible a' ∧ EqE ((Term.unary .snd (.var 1) : Recipe 3).subst σ) a' ∧
      ((∃ i : Fin 2, ∃ j, j < fieldCount 1 ∧
        (Term.unary .snd (.var 1) : Recipe 3) = (Term.var i.succ).drop j) ∨
          BaseEq target (.unary .fst a')) ∧ ¬ BaseEq target (.unary .fst a') := by
  obtain ⟨a', ha, hi⟩ := exists_normal_form ((Term.unary .snd (.var 1) : Recipe 3).subst σ)
  refine ⟨a', hi, ha.sound, ?_, ?_⟩
  · exact minimum_projection_normal_form ns false 0 1 ns.nonceNames .fst (Or.inl rfl)
      (.unary .snd (.var 1)) (HistoricalSelectorSPOT.second_minimal _)
      hi HistoricalSelectorSPOT.target_irreducible ha.sound HistoricalSelectorSPOT.second_evaluation
  · exact fun h => by cases h.head_eq

abbrev pairRecipe : Recipe 3 := .binary .pair (.name 40) (.name 41)
abbrev projectedPair : Recipe 3 := .unary .fst (.binary .pair pairRecipe (.const .bottom))

theorem minimality_required_for_pair_origin :
    EqE (projectedPair.subst σ) (.binary .pair (.name 40) (.name 41)) ∧
    ¬ PairRecipeOrigin projectedPair ∧ ¬ MinimalRecipe ns.nonceNames σ projectedPair := by
  refine ⟨(RootStep.fst _ _).sound, ?_, ?_⟩
  · rintro (⟨a, b, he⟩ | ⟨v, hc⟩)
    · cases he
    · cases hc with
      | step f hf h => cases h
  · exact fun hm => hm.raw_irreducible _ (RootStep.fst pairRecipe (.const .bottom)).to_rewrite

/-- Exact n=0 counterexample retained from the finite-catalogue gate. -/
theorem minimized_pair_origin_failure :
    let r : Recipe 3 := .unary .fst
      (.binary .pair (.binary .pair (.name 0) (.name 44)) (.const .bottom))
    ¬ PairRecipeOrigin r ∧ ReducesModulo (r.subst σ) (.binary .pair (.name 0) (.name 44)) := by
  dsimp only
  refine ⟨?_, .single (RootStep.fst _ _).to_modulo⟩
  rintro (⟨a, b, he⟩ | ⟨v, hc⟩)
  · cases he
  · cases hc with
    | step f hf h => cases h

/-- The source's actual frame is load-bearing: an arbitrary one-node published
ciphertext has no strictly smaller plaintext certificate. -/
theorem arbitrary_frame_generalization_refuted :
    let τ : Fin 1 → Ground := fun _ => target
    MinimalRecipe ns.nonceNames τ (.var 0) ∧ EqE ((Term.var 0).subst τ) target ∧
      ¬ (∃ p s, CiphertextProduct τ key (.var 0) p s) := by
  dsimp only
  refine ⟨MinimalRecipe.of_nodeCount_one trivial rfl, .refl _, ?_⟩
  rintro ⟨p, s, hp⟩
  have hlt := hp.plaintext_smaller
  have hpos := p.nodeCount_pos
  simp only [Term.nodeCount] at hlt
  omega

theorem minimum_selector_reducible_key :
    let k : Ground := .unary .fst (.binary .pair key (.const .bottom))
    ∃ p s, CiphertextProduct σ k second p s := by
  dsimp only
  have hk := (RootStep.fst key (.const .bottom)).sound
  have he := HistoricalSelectorSPOT.second_evaluation.trans
    (.ternary .penc hk.symm (.refl _) (.refl _))
  obtain ⟨p, s, hp, _⟩ := minimum_ciphertext_certificate ns false 0 1 ns.nonceNames second
    (HistoricalSelectorSPOT.second_minimal _) he
  exact ⟨p, s, hp⟩

abbrev first : Recipe 3 := (Term.var 1).project 0
abbrev mixed : Recipe 3 := .binary .mul (.ternary .penc (.var 0) (.name 40) (.name 41))
  (.binary .mul first first)
abbrev mixedPlaintext : Ground := .binary .add (.name 41) (.binary .add (.const .one) (.const .one))
abbrev mixedNonce : Ground := .binary .compose (.name 40) (.binary .compose (.name 20) (.name 20))

/-- The minimum representative retains a constructed plaintext and two copies
of an honest vote. The source product itself is not assumed minimum. -/
theorem mixed_minimum_reconstruction :
    ∃ r p s, MinimalRecipe ns.nonceNames σ r ∧
      EqE (r.subst σ) (.ternary .penc key mixedNonce mixedPlaintext) ∧
      CiphertextRecipeForm 1 r ∧ CiphertextProduct σ key r p s ∧
      p.Public ns.nonceNames ∧ p.nodeCount < r.nodeCount ∧
      EqE s mixedNonce ∧ EqE (p.subst σ) mixedPlaintext := by
  have hc : CiphertextProduct σ key mixed
      (.binary .add (.name 41) (.binary .add (.const .one) (.const .one))) mixedNonce :=
    .mul (.constructed (.var 0) (.name 40) (.name 41) (.refl _))
      (.mul (honest_projection_product ns false 0 1 0 0) (honest_projection_product ns false 0 1 0 0))
  have hpublic : mixed.Public ns.nonceNames := by
    change (True ∧ 40 ∉ ns.nonceNames ∧ 41 ∉ ns.nonceNames) ∧ True ∧ True
    decide
  obtain ⟨r, hr, he⟩ := exists_minimal_recipe (σ := σ) mixed hpublic
  have hv : EqE (r.subst σ) (.ternary .penc key mixedNonce mixedPlaintext) := he.symm.trans hc.sound
  obtain ⟨p, s, hp, hpub, hsize, hn, hm⟩ :=
    minimum_ciphertext_certificate ns false 0 1 ns.nonceNames r hr hv
  exact ⟨r, p, s, hr, hv, minimum_ciphertext_form ns false 0 1 ns.nonceNames r hr hv,
    hp, hpub, hsize, hn, hm⟩

abbrev projectedCiphertext : Recipe 3 := .unary .fst
  (.binary .pair (.ternary .penc (.var 0) (.name 40) (.name 41)) (.const .bottom))

theorem minimality_required_for_ciphertext_syntax :
    EqE (projectedCiphertext.subst σ) (.ternary .penc key (.name 40) (.name 41)) ∧
    ¬ CiphertextRecipeSyntax projectedCiphertext ∧
    ¬ MinimalRecipe ns.nonceNames σ projectedCiphertext := by
  refine ⟨(RootStep.fst _ _).sound, ?_, ?_⟩
  · intro hs
    cases hs with
    | selected v hc =>
      cases hc with
      | step f hf h => cases h
  · exact fun hm => hm.raw_irreducible _ (RootStep.fst _ _).to_rewrite

theorem mixed_plaintext_not_constant (c : Constant) : ¬ EqE mixedPlaintext (.const c) := by
  intro h
  have hv := h.denote (fun _ => 5) (fun _ => 0)
  cases c <;> simp [Term.denote, Term.interpretBinary] at hv

theorem honest_proof_minimum_form_exists :
    ∃ r, MinimalRecipe ns.nonceNames σ r ∧ r.nodeCount ≤ 4 ∧
      EqE (r.subst σ) ProjectionChainSPOT.p₀ ∧ ProofRecipeForm 1 r := by
  obtain ⟨r, hr, he⟩ := exists_minimal_recipe (σ := σ)
    ProjectionChainSPOT.proofRecipe (by trivial)
  have hv := he.symm.trans ProjectionChainSPOT.proof_positions_reach_fixed.1
  exact ⟨r, hr, hr.least ProjectionChainSPOT.proofRecipe (by trivial) he.symm,
    hv, minimum_proof_form ns false 0 1 ns.nonceNames r hr hv⟩

abbrev mixedPlainRecipe : Recipe 3 := .binary .add (.name 41) (.binary .add (.const .one) (.const .one))

/-- Knowing the key permits this successful decrypt; its smaller public
plaintext makes it nonminimum, exactly as the general theorem requires. -/
theorem successful_decryption_is_nonminimum :
    EqE ((Term.binary .dec (.name 10) mixed : Recipe 3).subst σ) mixedPlaintext ∧
      ¬ MinimalRecipe ns.nonceNames σ (.binary .dec (.name 10) mixed) := by
  have hc : CiphertextProduct σ key mixed mixedPlainRecipe mixedNonce :=
    .mul (.constructed (.var 0) (.name 40) (.name 41) (.refl _))
      (.mul (honest_projection_product ns false 0 1 0 0) (honest_projection_product ns false 0 1 0 0))
  have he : EqE ((Term.binary .dec (.name 10) mixed : Recipe 3).subst σ) mixedPlaintext :=
    (EqE.binary .dec (.refl _) hc.sound).trans (RootStep.decrypt _ _ _).sound
  refine ⟨he, ?_⟩
  intro hm
  apply hm.no_smaller (s := mixedPlainRecipe) (by change 41 ∉ ns.nonceNames ∧ True ∧ True; decide) he
  decide

end ExplainableCrypto.Helios.Symbolic.MinimumOriginSPOT
