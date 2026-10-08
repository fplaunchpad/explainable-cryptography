import ExplainableCrypto.Helios.Symbolic.PairObservationInduction
import ExplainableCrypto.Helios.Symbolic.PartialDecryptionObservationSPOT

namespace ExplainableCrypto.Helios.Symbolic.PairObservationSPOT
open Historical General
abbrev names := ProofObservationSPOT.names
abbrev left := ProofObservationSPOT.left
abbrev right := ProofObservationSPOT.right
abbrev world := ProofObservationSPOT.world
abbrev tail (i : Fin 2) (k : Nat) : Recipe 3 := (Term.var i.succ).drop k
abbrev rebuild : Recipe 3 := .binary .pair (.unary .fst (.var 1)) (.unary .snd (.var 1))
abbrev truncated : Recipe 3 := .binary .pair (.unary .fst (.var 1)) (.const .bottom)
abbrev wrapper : Recipe 3 := .unary .fst (.binary .pair (.var 1) (.const .bottom))

/-- The identity criterion covers every nonempty tail in both fixture worlds,
including reducible candidate representatives. -/
theorem fresh_tail_identity (swap : Bool) (i j : Fin 2) (k l : Nat) (hk : k < 5) (hl : l < 5) :
    EqE ((world swap).eval (tail i k)) ((world swap).eval (tail j l)) ↔ i = j ∧ k = l :=
  ballot_tail_equality_iff names HistoricalFrameSPOT.fixture_names_fresh swap left right i j k l hk hl

/-- Omitting nonemptiness loses voter identity: both distinct public tails reach
the same literal bottom at the first empty position. -/
theorem empty_tails_coincide (swap : Bool) :
    tail 0 5 ≠ tail 1 5 ∧
    EqE ((world swap).eval (tail 0 5)) (.const .bottom) ∧
    EqE ((world swap).eval (tail 1 5)) (.const .bottom) ∧
    EqE ((world swap).eval (tail 0 5)) ((world swap).eval (tail 1 5)) := by
  have h (i : Fin 2) : EqE ((world swap).eval (tail i 5)) (.const .bottom) := by
    have ht := ballot_tail_recipe_value names swap left right i 5 (by decide)
    have hl : (ballotFields names i (choice swap left right i).value).length = 5 := ballot_fields_length _ _ _
    simpa only [← hl, List.drop_length, Term.tuple] using ht
  exact ⟨by decide, h 0, h 1, (h 0).trans (h 1).symm⟩

/-- Colliding honest nonces with equal messages make distinct voters' entire
nonempty ballots equal. Freshness is load-bearing for the identity criterion. -/
theorem tail_freshness_required :
    EqE ((frame ProofObservationSPOT.colliding false right right).eval (tail 0 0))
      ((frame ProofObservationSPOT.colliding false right right).eval (tail 1 0)) ∧
    ¬ ProofObservationSPOT.colliding.Fresh :=
  ⟨.refl _, ProofObservationSPOT.freshness_required.2⟩

/-- Equal component/aggregate heads at one candidate do not identify whole
suffixes: the tails still have different numbers of pair cells. -/
theorem equal_fields_distinct_tails (swap : Bool) :
    EqE ((ProofObservationSPOT.oneWorld swap).eval ((Term.var 1).project 1))
      ((ProofObservationSPOT.oneWorld swap).eval ((Term.var 1).project 2)) ∧
    ¬ EqE ((ProofObservationSPOT.oneWorld swap).eval (tail 0 1))
      ((ProofObservationSPOT.oneWorld swap).eval (tail 0 2)) := by
  refine ⟨(ProofObservationSPOT.one_candidate_fields_coincide swap).2, ?_⟩
  intro he
  have hk := ((ballot_tail_equality_iff ProofObservationSPOT.oneNames NumericReflectionSPOT.fixture_names_fresh
    swap ProofObservationSPOT.oneLeft ProofObservationSPOT.oneRight 0 0 1 2 (by decide) (by decide)).mp he).2
  omega

/-- A public pair reconstructs the whole ballot from both projections. Replacing
its second member with bottom truncates real fields and changes the value. -/
theorem constructed_pair_and_truncation (swap : Bool) :
    rebuild.Public names.restricted ∧ truncated.Public names.restricted ∧
    EqE ((world swap).eval rebuild) ((world swap).eval (.var 1)) ∧
    ¬ EqE ((world swap).eval truncated) ((world swap).eval (.var 1)) := by
  obtain ⟨a, b, hv⟩ := ballot_tail_pair_value names swap left right 0 0 (by decide)
  refine ⟨by trivial, by trivial, (pair_reconstruction_of_value hv).symm, ?_⟩
  intro he
  have hs := ((pair_equality_iff_projections _ _ _ ⟨a, b, hv⟩).mp he).2
  obtain ⟨x, y, hp⟩ := ballot_tail_pair_value names swap left right 0 1 (by decide)
  have h := tuple_eqE_pair_nonempty ([] : List Ground) (hs.trans hp)
  simp at h

/-- Pair eta is valid for the supplied pair value above, but not for an
arbitrary public name. The observation transfer retains its pair-value premise. -/
theorem pair_value_premise_required :
    ¬ EqE (Term.name (V := Empty) 40)
      (.binary .pair (.unary .fst (.name 40)) (.unary .snd (.name 40))) := by
  intro he
  obtain ⟨_, _, hshape, _⟩ := he.symm.passive_binary_irreducible_shape (Or.inl rfl) (name_irreducible 40)
  cases hshape

/-- Without minimum size, a projection wrapper lies outside both exact forms
while returning an actual ballot pair. The public handle is smaller. -/
theorem minimum_origin_needs_minimum (swap : Bool) :
    wrapper.Public names.restricted ∧ EqE ((world swap).eval wrapper) ((world swap).eval (.var 1)) ∧
    ¬ PairObservationForm 1 wrapper ∧ ¬ MinimalRecipe names.restricted (world swap).value wrapper := by
  have he : EqE ((world swap).eval wrapper) ((world swap).eval (.var 1)) := (RootStep.fst _ _).sound
  refine ⟨by trivial, he, ?_, fun hm => hm.no_smaller (s := .var 1) trivial he (by decide)⟩
  rintro (⟨a, b, h⟩ | ⟨i, k, _, h⟩)
  · cases h
  · cases k with
    | zero => cases h
    | succ k => rw [Term.drop_succ_outer] at h; cases h

/-- The full minimum-pair interface is inhabited by two unequal one-node ballot
handles in the actual different-vote worlds. No test has total size below two,
so this is a checked base case of the bounded interface. -/
theorem minimum_pair_step_inhabited :
    MinimalRecipe names.restricted (world false).value (.var 1) ∧
    MinimalRecipe names.restricted (world false).value (.var 2) ∧
    ¬ EqE ((world false).eval (.var 1)) ((world false).eval (.var 2)) ∧
    (EqE ((world false).eval (.var 1)) ((world false).eval (.var 2)) ↔
      EqE ((world true).eval (.var 1)) ((world true).eval (.var 2))) := by
  have hr : MinimalRecipe names.restricted (world false).value (.var 1) :=
    MinimalRecipe.of_nodeCount_one trivial rfl
  have hs : MinimalRecipe names.restricted (world false).value (.var 2) :=
    MinimalRecipe.of_nodeCount_one trivial rfl
  obtain ⟨a, b, hva⟩ := ballot_tail_pair_value names false left right 0 0 (by decide)
  obtain ⟨c, d, hvb⟩ := ballot_tail_pair_value names false left right 1 0 (by decide)
  have hobs : (world false).ObservationsBelow (world true) 2 := by
    intro r s _ _ hsize
    have := r.nodeCount_pos
    have := s.nodeCount_pos
    omega
  refine ⟨hr, hs, ?_, minimum_pair_equality_swap names HistoricalFrameSPOT.fixture_names_fresh
    left right (.var 1) (.var 2) hr hs hva hvb hobs⟩
  intro he
  have hi := ((fresh_tail_identity false 0 1 0 0 (by decide) (by decide)).mp he).1
  exact (by decide : (0 : Fin 2) ≠ 1) hi

/-- Constructed/constructed and both constructed/tail orientations inhabit the
form-transfer interface. The constructed names retain their ordered inequality;
diagonal assignments discharge the bounded premise at nontrivial sizes. -/
theorem pair_form_matrix_inhabited :
    let φ := frame names false left left
    let ψ := frame names true left left
    let p : Recipe 3 := .binary .pair (.name 40) (.name 50)
    let q : Recipe 3 := .binary .pair (.name 50) (.name 40)
    ¬ EqE (φ.eval p) (φ.eval q) ∧
    (EqE (φ.eval p) (φ.eval q) ↔ EqE (ψ.eval p) (ψ.eval q)) ∧
    (EqE (φ.eval rebuild) (φ.eval (.var 1)) ↔ EqE (ψ.eval rebuild) (ψ.eval (.var 1))) ∧
    (EqE (φ.eval (.var 1)) (φ.eval rebuild) ↔ EqE (ψ.eval (.var 1)) (ψ.eval rebuild)) := by
  dsimp only
  have hp : (Term.binary .pair (.name 40) (.name 50) : Recipe 3).Public names.restricted := by
    change 40 ∉ names.restricted ∧ 50 ∉ names.restricted; decide
  have hq : (Term.binary .pair (.name 50) (.name 40) : Recipe 3).Public names.restricted := by
    change 50 ∉ names.restricted ∧ 40 ∉ names.restricted; decide
  have ht : PairObservationForm 1 (.var 1) := Or.inr ⟨0, 0, by decide, rfl⟩
  have hb : PairObservationForm 1 rebuild := Or.inl ⟨_, _, rfl⟩
  have transfer := pair_form_equality_swap names HistoricalFrameSPOT.fixture_names_fresh left left
  refine ⟨?_, transfer _ _ hp hq (Or.inl ⟨_, _, rfl⟩) (Or.inl ⟨_, _, rfl⟩)
    (CiphertextObservationSPOT.diagonal_observations _),
    transfer _ _ (by trivial) (by trivial) hb ht (CiphertextObservationSPOT.diagonal_observations _),
    transfer _ _ (by trivial) (by trivial) ht hb (CiphertextObservationSPOT.diagonal_observations _)⟩
  intro he
  have hn := (EqE.name_iff 40 50).mp ((EqE.pair_iff _ _ _ _).mp he).1
  omega

end ExplainableCrypto.Helios.Symbolic.PairObservationSPOT
