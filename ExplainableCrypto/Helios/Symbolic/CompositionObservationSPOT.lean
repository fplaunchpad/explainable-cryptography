import ExplainableCrypto.Helios.Symbolic.CompositionObservationInduction
import ExplainableCrypto.Helios.Symbolic.ValueShapeSPOT

namespace ExplainableCrypto.Helios.Symbolic.CompositionObservationSPOT
open Historical General
abbrev names := ProofObservationSPOT.names
abbrev left := ProofObservationSPOT.left
abbrev right := ProofObservationSPOT.right
abbrev world := ProofObservationSPOT.world
abbrev reveal := StuckDestructorSPOT.reveal
abbrev composed (x y : Nat) : Recipe 3 := .binary .compose (.name x) (.name y)

private theorem name_atom (n : Nat) : (Term.name (V := Empty) n).fullClass.ComposeAtom := by
  intro a b he
  exact arithmetic_not_eqE_name .compose (Or.inr rfl) a b n ((fullClass_eq_iff _ _).mp he).symm

private theorem named_factors (a b : Nat) :
    (Term.binary .compose (.name a) (.name b) : Ground).AtomicComposeFactors := by
  intro q hq
  simp only [Term.composeValueFactors, Multiset.mem_add, Multiset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact name_atom a
  · exact name_atom b

abbrev threeLeft : Ground := .binary .compose (reveal (.name 40)) (.binary .compose (.name 41) (.name 40))
abbrev threeRight : Ground := .binary .compose (.binary .compose (.name 40) (.name 40)) (.name 41)

/-- A reducible factor, reassociation and permutation preserve all three
occurrences. The full-E factor theorem is instantiated with semantic atoms. -/
theorem reducible_reassociation :
    threeLeft.AtomicComposeFactors ∧ threeRight.AtomicComposeFactors ∧
    threeLeft.composeValueFactors = threeRight.composeValueFactors ∧ EqE threeLeft threeRight := by
  have h40 : (reveal (.name 40)).fullClass = (Term.name (V := Empty) 40).fullClass :=
    (fullClass_eq_iff _ _).mpr (RootStep.fst _ _).sound
  have hl : threeLeft.AtomicComposeFactors := by
    intro q hq
    simp only [Term.composeValueFactors, h40, Multiset.mem_add, Multiset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact name_atom 40
    · exact name_atom 41
    · exact name_atom 40
  have hr : threeRight.AtomicComposeFactors := by
    intro q hq
    simp only [Term.composeValueFactors, Multiset.mem_add, Multiset.mem_singleton] at hq
    rcases hq with (rfl | rfl) | rfl
    · exact name_atom 40
    · exact name_atom 40
    · exact name_atom 41
  have hbag : threeLeft.composeValueFactors = threeRight.composeValueFactors := by
    simp only [Term.composeValueFactors, h40]
    ac_rfl
  exact ⟨hl, hr, hbag, (eqE_iff_compose_value_factors _ _ hl hr).mpr hbag⟩

/-- The input-0 duplicate-deletion witness: two occurrences of one name do not
collapse to one occurrence under full E. -/
theorem duplicates_are_observable :
    ¬ EqE (.binary .compose (.name 40) (.name 40) : Ground) (.name 40) := by
  have hn : (Term.name (V := Empty) 40).AtomicComposeFactors := by
    intro q hq
    have h : q = (Term.name (V := Empty) 40).fullClass := by simpa [Term.composeValueFactors] using hq
    subst q
    exact name_atom 40
  intro he
  have hc := congrArg Multiset.card ((eqE_iff_compose_value_factors _ _ (named_factors 40 40) hn).mp he)
  simp [Term.composeValueFactors] at hc

abbrev hidden : Ground := reveal (.binary .compose (.name 40) (.name 41))

/-- The input-0 missing-atom witness: a projection exposes two factors from one
raw leaf. Equality holds, but the raw full-E factor bags have different sizes. -/
theorem hidden_composition_requires_atom :
    EqE hidden (.binary .compose (.name 40) (.name 41)) ∧
    hidden.composeValueFactors ≠ (Term.binary .compose (.name 40) (.name 41) : Ground).composeValueFactors ∧
    ¬ hidden.AtomicComposeFactors := by
  have he : EqE hidden (.binary .compose (.name 40) (.name 41)) := (RootStep.fst _ _).sound
  refine ⟨he, ?_, ?_⟩
  · intro h
    have hc := congrArg Multiset.card h
    simp [hidden, reveal, StuckDestructorSPOT.reveal, Term.composeValueFactors] at hc
  · intro h
    exact h hidden.fullClass (by simp [hidden, reveal, StuckDestructorSPOT.reveal, Term.composeValueFactors])
      (.name 40) (.name 41) ((fullClass_eq_iff _ _).mpr he)

/-- Composition has no zero unit even though addition collapses zero-plus-one. -/
theorem composition_has_no_zero_unit :
    EqE (.binary .add (.const .zero) (.const .one) : Ground) (.const .one) ∧
    ¬ EqE (.binary .compose (.const .zero) (.name 40) : Ground) (.name 40) :=
  ⟨.equation .zero_one, arithmetic_not_eqE_name .compose (Or.inr rfl) _ _ 40⟩

/-- Public literal compositions attain the exact three-node minimum in actual
initial frames, including repeated names and arbitrary candidate assignments. -/
theorem literal_compose_minimum (swap : Bool) (a b : CandidateSubstitution 1 Empty)
    (x y : Nat) (hx : x ∉ names.restricted) (hy : y ∉ names.restricted) :
    MinimalRecipe names.restricted (General.frame names swap a b).value (composed x y) := by
  have hp : (composed x y).Public names.restricted := ⟨hx, hy⟩
  obtain ⟨r, hr, he⟩ := exists_minimal_recipe (σ := (General.frame names swap a b).value) _ hp
  obtain ⟨u, v, rfl⟩ := minimum_compose_form names swap a b names.restricted r hr he.symm
  refine ⟨hp, fun s hs hes => ?_⟩
  have hle := hr.least s hs (he.symm.trans hes)
  have := u.nodeCount_pos
  have := v.nodeCount_pos
  simp only [Term.nodeCount] at hle ⊢
  omega

/-- Distinct three-node minimum recipes commute. The complete branch is used
with a reducible supplied target and an inhabited six-node observation bound. -/
theorem permuted_minimum_step :
    (composed 40 41) ≠ (composed 41 40) ∧
    EqE ((General.frame names true left left).eval (composed 40 41))
      ((General.frame names true left left).eval (composed 41 40)) := by
  have hr := literal_compose_minimum false left left 40 41 (by decide) (by decide)
  have hs := literal_compose_minimum false left left 41 40 (by decide) (by decide)
  have he : EqE ((General.frame names false left left).eval (composed 40 41))
      (.binary .compose (reveal (.name 40)) (.name 41)) :=
    .binary .compose (RootStep.fst _ _).sound.symm (.refl _)
  exact ⟨by decide, (minimum_composition_equality_swap names left left _ _ hr hs he (.refl _)
    (CiphertextObservationSPOT.diagonal_observations _)).mp (.equation (.comm .compose trivial _ _))⟩

/-- A changed factor multiplicity remains observable in the complete minimum
branch. Thus permutation support cannot pass by equating every composition. -/
theorem unequal_minimum_step :
    ¬ EqE ((General.frame names false left left).eval (composed 40 41))
      ((General.frame names false left left).eval (composed 40 40)) ∧
    (EqE ((General.frame names false left left).eval (composed 40 41))
        ((General.frame names false left left).eval (composed 40 40)) ↔
      EqE ((General.frame names true left left).eval (composed 40 41))
        ((General.frame names true left left).eval (composed 40 40))) := by
  have hr := literal_compose_minimum false left left 40 41 (by decide) (by decide)
  have hs := literal_compose_minimum false left left 40 40 (by decide) (by decide)
  refine ⟨?_, minimum_composition_equality_swap names left left _ _ hr hs (.refl _) (.refl _)
    (CiphertextObservationSPOT.diagonal_observations _)⟩
  intro he
  have hbag := (eqE_iff_compose_value_factors _ _ (named_factors 40 41) (named_factors 40 40)).mp he
  have hsingle := add_left_cancel hbag
  have hclass := Multiset.singleton_inj.mp hsingle
  have hn := (EqE.name_iff 41 40).mp ((fullClass_eq_iff _ _).mp hclass)
  omega

abbrev wrapper : Recipe 3 := .unary .fst (.binary .pair (composed 40 41) (.const .bottom))

/-- Public nonminimum wrappers can have a composition value with another raw
head. Minimum size is necessary for the exact-origin argument. -/
theorem origin_needs_minimum (swap : Bool) :
    wrapper.Public names.restricted ∧
    EqE ((world swap).eval wrapper) ((world swap).eval (composed 40 41)) ∧
    ¬ (∃ a b : Recipe 3, wrapper = .binary .compose a b) ∧
    ¬ MinimalRecipe names.restricted (world swap).value wrapper := by
  have hp : (composed 40 41).Public names.restricted := by change 40 ∉ names.restricted ∧ 41 ∉ names.restricted; decide
  have he : EqE ((world swap).eval wrapper) ((world swap).eval (composed 40 41)) := (RootStep.fst _ _).sound
  refine ⟨⟨hp, trivial⟩, he, ?_, fun hm => hm.no_smaller hp he (by decide)⟩
  rintro ⟨a, b, h⟩
  cases h

end ExplainableCrypto.Helios.Symbolic.CompositionObservationSPOT
