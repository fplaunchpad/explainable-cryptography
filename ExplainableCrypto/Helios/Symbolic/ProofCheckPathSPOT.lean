import ExplainableCrypto.Helios.Symbolic.MinimalProofChecking
import ExplainableCrypto.Helios.Symbolic.ProofCheckSeparation
import ExplainableCrypto.Helios.Symbolic.MinimalDecryption
import ExplainableCrypto.Helios.Symbolic.ProofCheckingSPOT
import ExplainableCrypto.Helios.Symbolic.Separation

namespace ExplainableCrypto.Helios.Symbolic.ProofCheckPathSPOT

abbrev reveal (t : Term Nat) : Term Nat := .unary .fst (.binary .pair t (.const .bottom))
abbrev cipher (bit : Constant) : Term Nat := .ternary .penc (.name 0) (.name 1) (.const bit)
abbrev proof (bit : Constant) : Term Nat := .spk (.name 0) (.name 1) (.const bit) (cipher bit)
abbrev delayed (bit : Constant) : Term Nat :=
  .ternary .checkspk (reveal (.name 0)) (reveal (cipher bit)) (reveal (proof bit))

theorem reveal_path (t : Term Nat) : ReducesModulo (reveal t) t :=
  .single (RootStep.fst t (.const .bottom)).to_modulo

/-- All three argument heads are projections initially; both bits still reach ok. -/
theorem delayed_match (bit : Constant) (hb : bit = .zero ∨ bit = .one) :
    ProofCheckMatch (reveal (.name 0)) (reveal (cipher bit)) (reveal (proof bit)) :=
  ⟨.name 0, .name 1, bit, hb, reveal_path _, reveal_path _, reveal_path _⟩

theorem delayed_success (bit : Constant) (hb : bit = .zero ∨ bit = .one) :
    (rootReduce (delayed bit)).isNone = true ∧ ReducesModulo (delayed bit) (.const .ok) :=
  ⟨by cases bit <;> decide, (delayed_match bit hb).reduces⟩

/-- The semantic characterization reconstructs the same fixed successful example. -/
theorem exact_component_characterization (bit : Constant) (hb : bit = .zero ∨ bit = .one) :
    EqE (delayed bit) (.const .ok) ∧
      ∃ r bit', (bit' = Constant.zero ∨ bit' = .one) ∧
        EqE (reveal (cipher bit)) (.ternary .penc (reveal (.name 0)) r (.const bit')) ∧
        EqE (reveal (proof bit)) (.spk (reveal (.name 0)) r (.const bit') (reveal (cipher bit))) := by
  have he := (delayed_match bit hb).reduces.sound
  exact ⟨he, (EqE.check_ok_iff_components _ _ _).mp he⟩

theorem components_suffice (bit : Constant) (hb : bit = .zero ∨ bit = .one) :
    EqE (delayed bit) (.const .ok) := by
  apply (EqE.check_ok_iff_components _ _ _).mpr
  exact ⟨.name 1, bit, hb,
    (reveal_path _).sound.trans (.ternary .penc (reveal_path _).sound.symm (.refl _) (.refl _)),
    (reveal_path _).sound.trans (.spk (reveal_path _).sound.symm (.refl _) (.refl _)
      (reveal_path _).sound.symm)⟩

theorem successful_checks_not_minimum (bit : Constant) (hb : bit = .zero ∨ bit = .one) :
    ¬ MinimalRecipe ∅ (Term.var : Nat → Term Nat) (delayed bit) := by
  intro h
  apply h.check_not_ok _ _ _
  simpa only [Term.subst_var] using (delayed_match bit hb).reduces.sound

/-- The deliberate always-retained-head failure is an actual checked path. -/
theorem literal_check_head_can_disappear :
    ReducesModulo (delayed .zero) (.const .ok) ∧
    ¬ (∃ a b c : Term Nat, (Term.const .ok : Term Nat) = .ternary .checkspk a b c) := by
  refine ⟨(delayed_match .zero (Or.inl rfl)).reduces, ?_⟩
  rintro ⟨a, b, c, he⟩
  cases he

/-- Altering only the proof's bound ciphertext is rejected under full E. -/
theorem changed_binding_rejected :
    ¬ EqE (.ternary .checkspk (.name 0) (cipher .zero)
      (.spk (.name 0) (.name 1) (.const .zero) (cipher .one))) (.const .ok) := by
  intro h
  obtain ⟨r, bit, _, _, hp⟩ := (EqE.check_ok_iff_components _ _ _).mp h
  have hbound := ((EqE.spk_iff _ _ _ _ _ _ _ _).mp hp).2.2.2
  have hbits := ((EqE.penc_iff _ _ _ _ _ _).mp hbound).2.2
  exact zero_not_one hbits.symm

theorem nonbit_rejected :
    ¬ EqE (.ternary .checkspk (.name 0) (cipher .bottom) (proof .bottom)) (.const .ok) := by
  intro h
  obtain ⟨r, bit, hbit, hc, _⟩ := (EqE.check_ok_iff_components _ _ _).mp h
  have hbits := ((EqE.penc_iff _ _ _ _ _ _).mp hc).2.2
  have he := (irreducible_eqE_iff_base (constant_irreducible .bottom)
    (constant_irreducible bit)).mp hbits
  rcases hbit with rfl | rfl <;> cases he.head_eq

/-- Raw matching misses E0-expanded vote fields, which still satisfy full-E checking. -/
theorem e0_only_success :
    (rootReduce ProofCheckingSPOT.backgroundSource).isNone = true ∧
    EqE ProofCheckingSPOT.backgroundSource (.const .ok) ∧
    ProofCheckMatch ProofCheckingSPOT.key ProofCheckingSPOT.expandedBallot
      ProofCheckingSPOT.expandedProof := by
  have he := ProofCheckingSPOT.background_vote_representatives.2.1.sound
  exact ⟨ProofCheckingSPOT.background_vote_representatives.1, he, (EqE.check_ok_iff _ _ _).mp he⟩

abbrev stuck : Term Nat := .ternary .checkspk (.var 0) (.var 1) (.var 2)
abbrev wrappedVariables (n : Nat) : Term Nat := reveal (.var n)

theorem stuck_irreducible : Irreducible stuck := by
  intro t hs
  rcases hs.ternary_cases with hr | ⟨a, ha, _⟩ | ⟨b, hb, _⟩ | ⟨c, hc, _⟩
  · obtain ⟨_, _, _, _, _, hb, _⟩ := hr.proof_check_cases
    cases hb.head_eq
  · exact var_irreducible 0 a ha
  · exact var_irreducible 1 b hb
  · exact var_irreducible 2 c hc

theorem wrapped_evaluation (r : Term Nat) : EqE (r.subst wrappedVariables) r := by
  simpa only [Term.subst_var] using
    r.subst_congr wrappedVariables Term.var (fun n => (reveal_path (.var n)).sound)

/-- A four-node minimum under a substitution with reducible handle values. -/
theorem stuck_minimum : MinimalRecipe ∅ wrappedVariables stuck := by
  have hm : MinimalRecipe ∅ (Term.var : Nat → Term Nat) stuck :=
    MinimalRecipe.of_irreducible_weight (by trivial) stuck_irreducible rfl
  refine ⟨by trivial, ?_⟩
  intro s hs he
  apply hm.least s hs
  simpa only [Term.subst_var] using
    (wrapped_evaluation stuck).symm.trans (he.trans (wrapped_evaluation s))

theorem minimum_with_real_argument_steps :
    MinimalRecipe ∅ wrappedVariables stuck ∧ stuck.nodeCount = 4 ∧
    ModuloStep (stuck.subst wrappedVariables)
      (.ternary .checkspk (.var 0) (reveal (.var 1)) (reveal (.var 2))) ∧
    ReducesModulo (stuck.subst wrappedVariables) stuck :=
  ⟨stuck_minimum, rfl,
    (RootStep.fst (.var 0) (.const .bottom)).to_modulo.context
      (.ternaryFirst .checkspk .hole (reveal (.var 1)) (reveal (.var 2))),
    ReducesModulo.ternary .checkspk (reveal_path _) (reveal_path _) (reveal_path _)⟩

theorem minimum_check_normal_form :
    BaseEq stuck (.ternary .checkspk (.var 0) (.var 1) (.var 2)) :=
  stuck_minimum.proof_check_normal_form _ _ _ (var_irreducible 0) (var_irreducible 1)
    (var_irreducible 2) stuck_irreducible (reveal_path _).sound (reveal_path _).sound
    (reveal_path _).sound (wrapped_evaluation stuck)

theorem minimum_check_cannot_succeed :
    ¬ ProofCheckMatch (wrappedVariables 0) (wrappedVariables 1) (wrappedVariables 2) ∧
    ¬ EqE (stuck.subst wrappedVariables) (.const .ok) :=
  ⟨stuck_minimum.no_proof_check_match _ _ _, stuck_minimum.check_not_ok _ _ _⟩

/-- An equivalent projection wrapper is reducible and lacks the retained literal head. -/
theorem normality_required_for_check_shape :
    EqE (stuck.subst wrappedVariables) (reveal stuck) ∧
    ¬ (∃ a b c, reveal stuck = .ternary .checkspk a b c) ∧ ¬ Irreducible (reveal stuck) := by
  refine ⟨(wrapped_evaluation stuck).trans (reveal_path stuck).sound.symm, ?_, ?_⟩
  · rintro ⟨a, b, c, he⟩
    cases he
  · exact fun h => h _ (RootStep.fst stuck (.const .bottom)).to_modulo

/-- Head exclusions apply to arbitrary reducible passive targets. -/
theorem passive_outputs_excluded :
    ¬ EqE (delayed .zero) (.ternary .penc (reveal (.name 0)) (.name 1) (.name 2)) ∧
    ¬ EqE (delayed .zero) (.binary .pair (reveal (.name 0)) (.name 1)) ∧
    ¬ EqE (delayed .zero) (.binary .partialDecrypt (reveal (.name 0)) (.name 1)) ∧
    ¬ EqE (delayed .zero) (.spk (reveal (.name 0)) (.name 1) (.name 2) (delayed .zero)) ∧
    ¬ EqE (delayed .zero) (.unary .pk (reveal (.name 0))) :=
  ⟨proof_check_not_eqE_penc _ _ _ _ _ _,
    proof_check_not_eqE_passive_binary .pair (Or.inl rfl) _ _ _ _ _,
    proof_check_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ _ _,
    proof_check_not_eqE_spk _ _ _ _ _ _ _, proof_check_not_eqE_pk _ _ _ _⟩

end ExplainableCrypto.Helios.Symbolic.ProofCheckPathSPOT
