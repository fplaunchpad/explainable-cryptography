import ExplainableCrypto.Helios.Symbolic.AdditionObservationInduction
import ExplainableCrypto.Helios.Symbolic.CompositionObservationSPOT

namespace ExplainableCrypto.Helios.Symbolic.AdditionObservationSPOT
open Historical General
abbrev names := ProofObservationSPOT.names
abbrev left := ProofObservationSPOT.left
abbrev right := ProofObservationSPOT.right
abbrev world := ProofObservationSPOT.world
abbrev reveal := StuckDestructorSPOT.reveal
abbrev added (x y : Nat) : Recipe 3 := .binary .add (.name x) (.name y)

private theorem name_atom (n : Nat) : (Term.name (V := Empty) n).fullClass.AddAtom := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b he
    exact arithmetic_not_eqE_name .add (Or.inl rfl) a b n ((fullClass_eq_iff _ _).mp he).symm
  · intro he
    exact name_not_eqE_const n .zero ((fullClass_eq_iff _ _).mp he)
  · intro he
    exact name_not_eqE_const n .one ((fullClass_eq_iff _ _).mp he)

private theorem named_factors (a b : Nat) :
    (Term.binary .add (.name a) (.name b) : Ground).AtomicAddFactors := by
  intro q hq
  simp only [Term.addValueSummary, AddSummary.combine, AddSummary.atom,
    Multiset.mem_add, Multiset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact name_atom a
  · exact name_atom b

private theorem zero_factors : (Term.const (V := Empty) .zero).AtomicAddFactors := by
  intro q hq
  exact False.elim (Multiset.notMem_zero q hq)
private theorem one_factors : (Term.const (V := Empty) .one).AtomicAddFactors := by
  intro q hq
  exact False.elim (Multiset.notMem_zero q hq)

abbrev mixed : Ground := .binary .add (reveal (.name 40))
  (.binary .add (.const .zero) (.binary .add (.const .one) (.binary .add (.const .one) (.name 40))))
abbrev expected : Ground := .binary .add (.binary .add (.name 40) (.name 40))
  (.binary .add (.const .one) (.const .one))

/-- A reducible atom and numeric reductions preserve two name occurrences and
exactly two ones. Present zero is absorbed only into an existing numeric part. -/
theorem reducible_mixed_reconstruction :
    mixed.AtomicAddFactors ∧ expected.AtomicAddFactors ∧
    mixed.addValueSummary = ⟨{(Term.name (V := Empty) 40).fullClass, (.name 40 : Ground).fullClass}, some 2⟩ ∧
    EqE mixed expected := by
  have h40 : (reveal (.name 40)).fullClass = (Term.name (V := Empty) 40).fullClass :=
    (fullClass_eq_iff _ _).mpr (RootStep.fst _ _).sound
  have hl : mixed.AtomicAddFactors := by
    intro q hq
    simp [reveal, StuckDestructorSPOT.reveal, Term.addValueSummary,
      AddSummary.combine, AddSummary.atom, AddSummary.number, h40] at hq
    subst q
    exact name_atom 40
  have hr : expected.AtomicAddFactors := by
    intro q hq
    simp [Term.addValueSummary, AddSummary.combine, AddSummary.atom, AddSummary.number] at hq
    subst q
    exact name_atom 40
  have hs : mixed.addValueSummary = ⟨{(Term.name (V := Empty) 40).fullClass, (.name 40 : Ground).fullClass}, some 2⟩ := by
    simp [reveal, StuckDestructorSPOT.reveal, Term.addValueSummary,
      AddSummary.combine, AddSummary.atom, AddSummary.number, numericAdd, h40]
  refine ⟨hl, hr, hs, (eqE_iff_add_value_summary _ _ hl hr).mpr ?_⟩
  rw [hs]
  simp [Term.addValueSummary, AddSummary.combine, AddSummary.atom, AddSummary.number, numericAdd]

/-- The numeric-presence mutation is false in full E, alongside both legal
numeric collapses. A present zero remains observable beside a nonnumeric atom. -/
theorem numeric_presence_is_observable :
    EqE (.binary .add (.const .zero) (.const .zero) : Ground) (.const .zero) ∧
    EqE (.binary .add (.const .zero) (.const .one) : Ground) (.const .one) ∧
    ¬ EqE (.binary .add (.name 40) (.const .zero) : Ground) (.name 40) := by
  refine ⟨.equation .zero_zero, .equation .zero_one, ?_⟩
  intro he
  have ha : (Term.binary .add (.name 40) (.const .zero) : Ground).AtomicAddFactors := by
    intro q hq
    simp [Term.addValueSummary, AddSummary.combine, AddSummary.atom, AddSummary.number] at hq
    subst q
    exact name_atom 40
  have hn := (Term.add_value_atom (name_atom 40)).2
  have h := (eqE_iff_add_value_summary _ _ ha hn).mp he
  exact AddSummary.atom_zero_not_atom _ h

/-- Positive numeric values retain their count; the two-one sum is not one. -/
theorem numeric_count_is_observable :
    ¬ EqE (.binary .add (.const .one) (.const .one) : Ground) (.const .one) := by
  intro he
  have ha : (Term.binary .add (.const .one) (.const .one) : Ground).AtomicAddFactors := by
    intro q hq
    simp [Term.addValueSummary, AddSummary.combine, AddSummary.number] at hq
  exact AddSummary.two_ones_not_one ((eqE_iff_add_value_summary _ _ ha one_factors).mp he)

/-- Atom multiplicity is independent of the numeric count. -/
theorem duplicates_are_observable : ¬ EqE (.binary .add (.name 40) (.name 40) : Ground) (.name 40) := by
  intro he
  have h := (eqE_iff_add_value_summary _ _ (named_factors 40 40) (Term.add_value_atom (name_atom 40)).2).mp he
  have hc := congrArg (fun s => s.atoms.card) h
  simp [Term.addValueSummary, AddSummary.combine, AddSummary.atom] at hc

abbrev hiddenZero : Ground := reveal (.const .zero)
abbrev hiddenAdd : Ground := reveal (.binary .add (.name 40) (.name 41))

/-- Input zero from the hidden-value gate: a projection reveals zero from a raw
atom. Its E-value agrees, while its numeric field changes from absent to present. -/
theorem hidden_numeric_requires_atom :
    EqE hiddenZero (.const .zero) ∧
    hiddenZero.addValueSummary ≠ (Term.const .zero : Ground).addValueSummary ∧
    ¬ hiddenZero.AtomicAddFactors := by
  have he : EqE hiddenZero (.const .zero) := (RootStep.fst _ _).sound
  refine ⟨he, ?_, ?_⟩
  · intro h
    have hn := congrArg AddSummary.numeric h
    cases hn
  · intro h
    exact (h hiddenZero.fullClass (by simp [hiddenZero, reveal, StuckDestructorSPOT.reveal,
      Term.addValueSummary, AddSummary.atom])).2.1 ((fullClass_eq_iff _ _).mpr he)

/-- Input one from the same gate: a projection exposes two summands from one raw
atom, so omission of the no-addition premise also fails independently. -/
theorem hidden_addition_requires_atom :
    EqE hiddenAdd (.binary .add (.name 40) (.name 41)) ∧
    hiddenAdd.addValueSummary ≠ (Term.binary .add (.name 40) (.name 41) : Ground).addValueSummary ∧
    ¬ hiddenAdd.AtomicAddFactors := by
  have he : EqE hiddenAdd (.binary .add (.name 40) (.name 41)) := (RootStep.fst _ _).sound
  refine ⟨he, ?_, ?_⟩
  · intro h
    have hc := congrArg (fun s => s.atoms.card) h
    simp [hiddenAdd, reveal, StuckDestructorSPOT.reveal, Term.addValueSummary, AddSummary.atom, AddSummary.combine] at hc
  · intro h
    exact (h hiddenAdd.fullClass (by simp [hiddenAdd, reveal, StuckDestructorSPOT.reveal,
      Term.addValueSummary, AddSummary.atom])).1 _ _ ((fullClass_eq_iff _ _).mpr he)

/-- Public literal name sums attain exact three-node minima in actual initial
frames, for repeated names and arbitrary valid candidate assignments. -/
theorem literal_add_minimum (swap : Bool) (a b : CandidateSubstitution 1 Empty)
    (x y : Nat) (hx : x ∉ names.restricted) (hy : y ∉ names.restricted) :
    MinimalRecipe names.restricted (General.frame names swap a b).value (added x y) := by
  have hp : (added x y).Public names.restricted := ⟨hx, hy⟩
  obtain ⟨r, hr, he⟩ := exists_minimal_recipe (σ := (General.frame names swap a b).value) _ hp
  rcases minimum_add_form names swap a b names.restricted r hr he.symm with ⟨u, v, rfl⟩ | rfl | rfl
  · refine ⟨hp, fun s hs hes => ?_⟩
    have hle := hr.least s hs (he.symm.trans hes)
    have := u.nodeCount_pos
    have := v.nodeCount_pos
    simp only [Term.nodeCount] at hle ⊢
    omega
  · have hn := congrArg AddSummary.numeric ((eqE_iff_add_value_summary _ _ (named_factors x y) zero_factors).mp he)
    cases hn
  · have hn := congrArg AddSummary.numeric ((eqE_iff_add_value_summary _ _ (named_factors x y) one_factors).mp he)
    cases hn

/-- Distinct permuted minima instantiate the full branch with a reducible
supplied target and an inhabited six-node smaller-observation premise. -/
theorem permuted_minimum_step :
    (added 40 41) ≠ (added 41 40) ∧
    EqE ((General.frame names true left left).eval (added 40 41))
      ((General.frame names true left left).eval (added 41 40)) := by
  have hr := literal_add_minimum false left left 40 41 (by decide) (by decide)
  have hs := literal_add_minimum false left left 41 40 (by decide) (by decide)
  have he : EqE ((General.frame names false left left).eval (added 40 41))
      (.binary .add (reveal (.name 40)) (.name 41)) :=
    .binary .add (RootStep.fst _ _).sound.symm (.refl _)
  exact ⟨by decide, (minimum_addition_equality_swap names left left _ _ hr hs he (.refl _)
    (CiphertextObservationSPOT.diagonal_observations _)).mp (.equation (.comm .add trivial _ _))⟩

/-- The complete minimum branch also retains unequal atom multiplicities. -/
theorem unequal_minimum_step :
    ¬ EqE ((General.frame names false left left).eval (added 40 41))
      ((General.frame names false left left).eval (added 40 40)) ∧
    (EqE ((General.frame names false left left).eval (added 40 41))
        ((General.frame names false left left).eval (added 40 40)) ↔
      EqE ((General.frame names true left left).eval (added 40 41))
        ((General.frame names true left left).eval (added 40 40))) := by
  have hr := literal_add_minimum false left left 40 41 (by decide) (by decide)
  have hs := literal_add_minimum false left left 40 40 (by decide) (by decide)
  refine ⟨?_, minimum_addition_equality_swap names left left _ _ hr hs (.refl _) (.refl _)
    (CiphertextObservationSPOT.diagonal_observations _)⟩
  intro he
  have hbag := congrArg AddSummary.atoms ((eqE_iff_add_value_summary _ _ (named_factors 40 41) (named_factors 40 40)).mp he)
  have hsingle := add_left_cancel hbag
  have hclass := Multiset.singleton_inj.mp hsingle
  have hn := (EqE.name_iff 41 40).mp ((fullClass_eq_iff _ _).mp hclass)
  omega

/-- One-node numeric minima instantiate the addition branch in different-vote
worlds. The supplied addition values collapse; literal add syntax is not required. -/
theorem numeric_minimum_step :
    ¬ EqE ((world false).eval (.const .zero)) ((world false).eval (.const .one)) ∧
    (EqE ((world false).eval (.const .zero)) ((world false).eval (.const .one)) ↔
      EqE ((world true).eval (.const .zero)) ((world true).eval (.const .one))) := by
  have hz : MinimalRecipe names.restricted (world false).value (.const .zero) :=
    MinimalRecipe.of_nodeCount_one trivial rfl
  have ho : MinimalRecipe names.restricted (world false).value (.const .one) :=
    MinimalRecipe.of_nodeCount_one trivial rfl
  refine ⟨zero_not_one, minimum_addition_equality_swap names left right _ _ hz ho
    (EqE.equation .zero_zero).symm (EqE.equation .zero_one).symm ?_⟩
  intro r s _ _ hsize
  have := r.nodeCount_pos
  have := s.nodeCount_pos
  simp only [Term.nodeCount] at hsize
  omega

abbrev wrapper : Recipe 3 := .unary .fst (.binary .pair (added 40 41) (.const .bottom))

/-- A public nonminimum wrapper has an addition value without addition/bit
syntax. Its smaller equivalent public recipe explains the failed origin premise. -/
theorem origin_needs_minimum (swap : Bool) :
    wrapper.Public names.restricted ∧
    EqE ((world swap).eval wrapper) ((world swap).eval (added 40 41)) ∧
    ¬ ((∃ a b : Recipe 3, wrapper = .binary .add a b) ∨ wrapper = .const .zero ∨ wrapper = .const .one) ∧
    ¬ MinimalRecipe names.restricted (world swap).value wrapper := by
  have hp : (added 40 41).Public names.restricted := by change 40 ∉ names.restricted ∧ 41 ∉ names.restricted; decide
  have he : EqE ((world swap).eval wrapper) ((world swap).eval (added 40 41)) := (RootStep.fst _ _).sound
  refine ⟨⟨hp, trivial⟩, he, ?_, fun hm => hm.no_smaller hp he (by decide)⟩
  rintro (⟨a, b, h⟩ | h | h) <;> cases h

end ExplainableCrypto.Helios.Symbolic.AdditionObservationSPOT
