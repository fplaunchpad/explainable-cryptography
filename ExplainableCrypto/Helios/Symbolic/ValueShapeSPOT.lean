import ExplainableCrypto.Helios.Symbolic.MinimumDestructorTransfer
import ExplainableCrypto.Helios.Symbolic.DecryptionProbeSPOT

namespace ExplainableCrypto.Helios.Symbolic.ValueShapeSPOT
open Historical General
abbrev names := ProofObservationSPOT.names
abbrev left : CandidateSubstitution 1 Empty := (BitCandidate.selected (0 : Fin 2)).substitution
abbrev right : CandidateSubstitution 1 Empty := (BitCandidate.abstain 1).substitution
abbrev world (swap : Bool) := General.frame names swap left right
abbrev first : Recipe 3 := .unary .fst (.var 1)

private theorem below_two (φ ψ : Frame names.restricted 3) : φ.ObservationsBelow ψ 2 := by
  intro r s _ _ hsize
  have := r.nodeCount_pos
  have := s.nodeCount_pos
  omega

private theorem diagonal (bound : Nat) :
    (General.frame names false left left).ObservationsBelow (General.frame names true left left) bound := by
  intro r s _ _ _
  exact Iff.rfl

private theorem first_value (swap : Bool) : EqE ((world swap).eval first)
    (General.ciphertext names 0 (General.choice swap left right 0).value 0) := by
  simpa [Frame.eval, first, Term.project, Term.drop, Term.subst, General.frame] using
    General.ballot_project_ciphertext names 0 (General.choice swap left right 0).value 0

private theorem first_minimum : MinimalRecipe names.restricted (world false).value first := by
  refine ⟨trivial, ?_⟩
  intro r _ he
  exact ciphertext_recipe_size_ge_two (world false).value _ _ _
    (fun v => General.frame_handle_not_ciphertext names false left right v _ _ _) (he.symm.trans (first_value false))

/-- An actual two-node ciphertext minimum keeps its value class across different
votes while its ciphertext E-value changes. Shape invariance is not value equality. -/
theorem ciphertext_shape_is_not_value_equality :
    ((world false).eval first).CiphertextValue ∧ ((world true).eval first).CiphertextValue ∧
    ¬ EqE ((world false).eval first) ((world true).eval first) := by
  have hv : ((world false).eval first).CiphertextValue := ⟨_, _, _, first_value false⟩
  have hswap := minimum_value_shapes_swap names left right first first_minimum (below_two _ _)
  refine ⟨hv, hswap.2.1.mp hv, ?_⟩
  intro he
  have hm := ((EqE.penc_iff _ _ _ _ _ _).mp ((first_value false).symm.trans (he.trans (first_value true)))).2.2
  exact zero_not_one hm.symm

/-- A public ballot handle is a one-node pair minimum, and a constructed partial
key is a three-node minimum. Both positive value classes inhabit the theorem. -/
theorem pair_and_partial_shape_instances :
    (((world false).eval (.var 1)).PairValue ↔ ((world true).eval (.var 1)).PairValue) ∧
    ((world true).eval (.var 1)).PairValue ∧
    ((General.frame names true left left).eval (.binary .partialDecrypt (.name 40) (.name 50))).PartialValue := by
  have hm : MinimalRecipe names.restricted (world false).value (.var 1) := MinimalRecipe.of_nodeCount_one trivial rfl
  have hpair := (minimum_value_shapes_swap names left right (.var 1) hm ((below_two _ _).mono (by decide))).1
  have hv := General.ballot_tail_pair_value names false left right 0 0 (by decide)
  have hp := PartialDecryptionObservationSPOT.literal_partial_minimum false left left 40 50 (by decide) (by decide)
  have hs := minimum_value_shapes_swap names left left (.binary .partialDecrypt (.name 40) (.name 50)) hp
    (diagonal _)
  exact ⟨hpair, hpair.mp hv, hs.2.2.mp ⟨_, _, .refl _⟩⟩

/-- The general decryption failure theorem covers named arguments, which have
neither partial-key nor ciphertext source values. It also covers a real honest
ciphertext and partial key through the earlier six-node fixture. -/
theorem arbitrary_argument_failure_instances :
    (∀ m, ¬ DecryptionMatch ((General.frame names true left left).eval (.name 40))
      ((General.frame names true left left).eval (.name 50)) m) ∧
    (∀ m, ¬ DecryptionMatch ((General.frame names true left left).eval (.binary .partialDecrypt (.name 40) (.name 50)))
      ((General.frame names true left left).eval first) m) := by
  exact ⟨minimum_decryption_failure_swap names left left (.name 40) (.name 50)
    (StuckDestructorSPOT.literal_decryption_minimum false left left 40 50 (by decide) (by decide))
    (diagonal _),
    minimum_decryption_failure_swap names left left _ _
      (DecryptionProbeSPOT.six_node_minimum false left left 50 (by decide)).1
      (diagonal _)⟩

private theorem named_no_match (a : Ground) (name : Nat) : ∀ m, ¬ DecryptionMatch a (.name name) m := by
  rintro m ⟨k, nonce, _, hb⟩
  obtain ⟨_, _, _, hs, _⟩ := hb.sound.symm.penc_irreducible_shape (name_irreducible name)
  cases hs

/-- Distinct three-node minima instantiate the complete value-based decryption
iff branch. Their named arguments rule out the former supplied-ciphertext case. -/
theorem unequal_decryption_branch :
    ¬ EqE ((General.frame names false left left).eval (StuckDestructorSPOT.decryption 40 50))
      ((General.frame names false left left).eval (StuckDestructorSPOT.decryption 40 51)) ∧
    (EqE ((General.frame names false left left).eval (StuckDestructorSPOT.decryption 40 50))
        ((General.frame names false left left).eval (StuckDestructorSPOT.decryption 40 51)) ↔
      EqE ((General.frame names true left left).eval (StuckDestructorSPOT.decryption 40 50))
        ((General.frame names true left left).eval (StuckDestructorSPOT.decryption 40 51))) := by
  have hr := StuckDestructorSPOT.literal_decryption_minimum false left left 40 50 (by decide) (by decide)
  have hs := StuckDestructorSPOT.literal_decryption_minimum false left left 40 51 (by decide) (by decide)
  refine ⟨?_, minimum_stuck_decryption_equality_swap names left left _ _ hr hs
    (named_no_match (.name 40) 50) (named_no_match (.name 40) 51) (.refl _) (.refl _)
    (diagonal _)⟩
  intro he
  have hn := (EqE.name_iff 50 51).mp ((EqE.decryption_iff_of_no_match _ _ _ _
    (named_no_match (.name 40) 50) (named_no_match (.name 40) 51)).mp he).2
  omega

private theorem snd_key_minimum : MinimalRecipe names.restricted (General.frame names false left left).value
    (.unary .snd (.var 0)) := by
  obtain ⟨r, hr, he⟩ := exists_minimal_recipe (σ := (General.frame names false left left).value)
    (.unary .snd (.var 0)) (by trivial)
  obtain ⟨u, rfl, _⟩ := minimum_stuck_projection_form names false left left names.restricted r hr .snd (Or.inr rfl)
    (fun x y => pk_not_eqE_pair _ x y) he.symm
  refine ⟨trivial, fun s hs hes => ?_⟩
  have hle := hr.least s hs (he.symm.trans hes)
  have := u.nodeCount_pos
  simp only [Term.nodeCount] at hle ⊢
  omega

/-- Different selectors over the election key are unequal two-node minima.
One supplied target has a reducible argument; the full projection iff theorem
retains the selector and derives destination no-pair facts. -/
theorem unequal_projection_branch :
    ¬ EqE ((General.frame names false left left).eval (.unary .fst (.var 0)))
      ((General.frame names false left left).eval (.unary .snd (.var 0))) ∧
    (EqE ((General.frame names false left left).eval (.unary .fst (.var 0)))
        ((General.frame names false left left).eval (.unary .snd (.var 0))) ↔
      EqE ((General.frame names true left left).eval (.unary .fst (.var 0)))
        ((General.frame names true left left).eval (.unary .snd (.var 0)))) := by
  have hr := StuckDestructorSPOT.literal_projection_minimum false left left
  have hp : ∀ x y, ¬ EqE (publicKey names : Ground) (.binary .pair x y) := fun x y => pk_not_eqE_pair _ x y
  have hw : EqE (StuckDestructorSPOT.reveal (publicKey names)) (publicKey names) := (RootStep.fst _ _).sound
  have hp' : ∀ x y, ¬ EqE (StuckDestructorSPOT.reveal (publicKey names)) (.binary .pair x y) :=
    fun x y he => hp x y (hw.symm.trans he)
  refine ⟨?_, minimum_stuck_projection_equality_swap names left left _ _ hr snd_key_minimum
    .fst .snd (Or.inl rfl) (Or.inr rfl) hp hp' (.refl _) (.unary .snd hw.symm)
    (diagonal _)⟩
  intro he
  have hf := ((EqE.projection_iff_of_no_pair .fst .snd (Or.inl rfl) (Or.inr rfl) _ _ hp hp).mp he).1
  cases hf

abbrev matched : Recipe 3 := .binary .dec (.name 40)
  (.ternary .penc (.unary .pk (.name 40)) (.name 50) (.binary .partialDecrypt (.name 60) (.name 61)))

/-- Public nonminimum destructors really succeed. A projection and E5 both
produce the expected partial value, refuting universal immediate stuckness. -/
theorem successful_destructors_need_minimum :
    matched.Public names.restricted ∧
    ((world false).eval matched).PartialValue ∧
    ¬ MinimalRecipe names.restricted (world false).value matched ∧
    (.unary .fst (.binary .pair (.binary .partialDecrypt (.name 40) (.name 50)) (.const .bottom)) : Ground).PartialValue := by
  have hp : (Term.binary .partialDecrypt (.name 60) (.name 61) : Recipe 3).Public names.restricted := by
    change 60 ∉ names.restricted ∧ 61 ∉ names.restricted; decide
  have he : EqE ((world false).eval matched) ((world false).eval (.binary .partialDecrypt (.name 60) (.name 61))) :=
    (RootStep.decrypt _ _ _).sound
  refine ⟨?_, ⟨_, _, he⟩, fun hm => hm.no_smaller hp he (by decide), ⟨_, _, (RootStep.fst _ _).sound⟩⟩
  change 40 ∉ names.restricted ∧ 40 ∉ names.restricted ∧ 50 ∉ names.restricted ∧ 60 ∉ names.restricted ∧ 61 ∉ names.restricted
  decide

abbrev leakedBit : Recipe 3 := .binary .dec (.name 10) first
abbrev policyAttack : Recipe 3 := .binary .mul
  (.ternary .penc leakedBit (.name 40) (.name 50))
  (.ternary .penc (.const .one) (.name 41) (.name 51))

/-- The gate's omitted-policy fixture decrypts a vote and uses it as a public
ciphertext key. One world fuses the product and the other cannot. This fixture
is not public under the theorem's policy; no minimum-size claim is made for it. -/
theorem secret_key_policy_shape_counterexample :
    ¬ policyAttack.Public names.restricted ∧
    ((world false).eval policyAttack).CiphertextValue ∧
    ¬ ((world true).eval policyAttack).CiphertextValue := by
  have hf : EqE ((world false).eval leakedBit) (.const .one) :=
    (EqE.binary .dec (.refl _) (first_value false)).trans (RootStep.decrypt _ _ _).sound
  have ht : EqE ((world true).eval leakedBit) (.const .zero) :=
    (EqE.binary .dec (.refl _) (first_value true)).trans (RootStep.decrypt _ _ _).sound
  refine ⟨?_, ?_, ?_⟩
  · intro hp
    have hn : 10 ∉ names.restricted := hp.1.1.1
    exact hn (by decide)
  · refine ⟨.const .one, .binary .compose (.name 40) (.name 41), .binary .add (.name 50) (.name 51), ?_⟩
    exact (EqE.binary .mul (.ternary .penc hf (.refl _) (.refl _)) (.refl _)).trans
      (RootStep.homomorphic _ _ _ _ _).sound
  · rintro ⟨k, nonce, p, he⟩
    obtain ⟨_, _, _, _, ha, hb, _⟩ := he.mul_penc_inversion
    have hka := ((EqE.penc_iff _ _ _ _ _ _).mp ha).1
    have hkb := ((EqE.penc_iff _ _ _ _ _ _).mp hb).1
    exact zero_not_one (ht.symm.trans (hka.trans hkb.symm))

end ExplainableCrypto.Helios.Symbolic.ValueShapeSPOT
