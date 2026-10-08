import ExplainableCrypto.Helios.Symbolic.AtomicObservationInduction
import ExplainableCrypto.Helios.Symbolic.PairObservationSPOT

namespace ExplainableCrypto.Helios.Symbolic.AtomicObservationSPOT
open Historical General
abbrev names := ProofObservationSPOT.names
abbrev left := ProofObservationSPOT.left
abbrev right := ProofObservationSPOT.right
abbrev world := ProofObservationSPOT.world
abbrev nameWrapper : Recipe 3 := .unary .fst (.binary .pair (.name 40) (.const .bottom))
abbrev honestCheck : Recipe 3 := .ternary .checkspk (.var 0)
  ((Term.var 1).project 0) ((Term.var 1).project 2)
abbrev gateNames : Names 0 := ⟨0, 1, fun i j => 2 + i.val + j.val⟩
abbrev gateWorld (swap : Bool) := General.frame gateNames swap
  (BitCandidate.abstain 0).substitution (BitCandidate.selected (0 : Fin 1)).substitution
abbrev emptyTail : Recipe 3 := (Term.var 1).drop 3

/-- Literal public names and all four constants attain the one-node minimum,
in either actual fixture world. Names are not restricted to a finite sample. -/
theorem literal_atoms_minimum (swap : Bool) (name : Nat) (hn : name ∉ names.restricted) (c : Constant) :
    MinimalRecipe names.restricted (world swap).value (.name name) ∧
    MinimalRecipe names.restricted (world swap).value (.const c) :=
  ⟨MinimalRecipe.of_nodeCount_one hn rfl, MinimalRecipe.of_nodeCount_one trivial rfl⟩

/-- E3/E4 give nonliteral atomic values without merging the bits. Both sums
have smaller public literal representatives and are therefore not minimum. -/
theorem arithmetic_bits_not_minimum (swap : Bool) :
    EqE ((world swap).eval (.binary .add (.const .zero) (.const .zero))) (.const .zero) ∧
    EqE ((world swap).eval (.binary .add (.const .zero) (.const .one))) (.const .one) ∧
    ¬ MinimalRecipe names.restricted (world swap).value (.binary .add (.const .zero) (.const .zero)) ∧
    ¬ MinimalRecipe names.restricted (world swap).value (.binary .add (.const .zero) (.const .one)) ∧
    ¬ EqE (Term.const (V := Empty) .zero) (.const .one) := by
  have hz : EqE ((world swap).eval (.binary .add (.const .zero) (.const .zero))) (.const .zero) :=
    .equation .zero_zero
  have ho : EqE ((world swap).eval (.binary .add (.const .zero) (.const .one))) (.const .one) :=
    .equation .zero_one
  exact ⟨hz, ho, fun hm => hm.no_smaller (s := .const .zero) trivial hz (by decide),
    fun hm => hm.no_smaller (s := .const .one) trivial ho (by decide), zero_not_one⟩

/-- A real successful component-proof check returns ok and has a smaller public
constant recipe, including with reducible valid candidate representatives. -/
theorem honest_check_not_minimum (swap : Bool) :
    honestCheck.Public names.restricted ∧ EqE ((world swap).eval honestCheck) (.const .ok) ∧
    ¬ MinimalRecipe names.restricted (world swap).value honestCheck := by
  have h := (honest_proofs_valid names 0 (choice swap left right 0).value
    (choice swap left right 0).valid).2 (0 : Fin 2)
  have he : EqE ((world swap).eval honestCheck) (.const .ok) := by
    simpa [honestCheck, Frame.eval, Term.subst, Term.subst_project, General.frame_voter_handle, General.frame] using h
  exact ⟨by trivial, he, fun hm => hm.no_smaller (s := .const .ok) trivial he (by decide)⟩

/-- The minimized omitted-minimum defect is an actual empty ballot tail.
It returns bottom, is nonliteral, and is strictly larger than public bottom. -/
theorem empty_tail_not_minimum (swap : Bool) :
    emptyTail.Public gateNames.restricted ∧ EqE ((gateWorld swap).eval emptyTail) (.const .bottom) ∧
    emptyTail ≠ .const .bottom ∧ ¬ MinimalRecipe gateNames.restricted (gateWorld swap).value emptyTail := by
  have he : EqE ((gateWorld swap).eval emptyTail) (.const .bottom) := by
    have ht := ballot_tail_recipe_value gateNames swap (BitCandidate.abstain 0).substitution
      (BitCandidate.selected (0 : Fin 1)).substitution 0 3 (by decide)
    have hl : (General.ballotFields gateNames 0 (General.choice swap (BitCandidate.abstain 0).substitution
        (BitCandidate.selected (0 : Fin 1)).substitution 0).value).length = 3 := General.ballot_fields_length _ _ _
    have hempty := List.drop_eq_nil_of_le (show (General.ballotFields gateNames 0 (General.choice swap
      (BitCandidate.abstain 0).substitution (BitCandidate.selected (0 : Fin 1)).substitution 0).value).length ≤ 3 by omega)
    simpa [hempty, Term.tuple, gateWorld, emptyTail] using ht
  exact ⟨by trivial, he, by decide, fun hm => hm.no_smaller (s := .const .bottom) trivial he (by decide)⟩

/-- A public projection wrapper has a name value without literal syntax or
minimum size. The nearby distinct public name still has a different E-value. -/
theorem name_wrapper_not_minimum (swap : Bool) :
    nameWrapper.Public names.restricted ∧ EqE ((world swap).eval nameWrapper) (.name 40) ∧
    nameWrapper ≠ .name 40 ∧ ¬ MinimalRecipe names.restricted (world swap).value nameWrapper ∧
    ¬ EqE ((world swap).eval nameWrapper) (.name 41) := by
  have hn : (Term.name 40 : Recipe 3).Public names.restricted := by change 40 ∉ names.restricted; decide
  have he : EqE ((world swap).eval nameWrapper) (.name 40) := (RootStep.fst _ _).sound
  refine ⟨⟨hn, trivial⟩, he, by decide, fun hm => hm.no_smaller hn he (by decide), ?_⟩
  intro he'
  have h := (EqE.name_iff 40 41).mp (he.symm.trans he')
  omega

abbrev publishedAtom (name : Nat) : Frame names.restricted 3 := ⟨fun _ => .name name⟩

/-- An arbitrary frame may publish an atom at a minimum handle. Changing that
frame changes the handle's value, so the source initial-frame premise cannot be
removed from literal syntax or exact evaluation transport. -/
theorem initial_frame_required :
    MinimalRecipe names.restricted (publishedAtom 40).value (.var 0) ∧
    EqE ((publishedAtom 40).eval (.var 0)) (.name 40) ∧
    (Term.var 0 : Recipe 3) ≠ .name 40 ∧
    (publishedAtom 41).eval (.var 0) ≠ .name 40 :=
  ⟨MinimalRecipe.of_nodeCount_one trivial rfl, .refl _, by decide, by decide⟩

/-- The caller's policy determines which literal name is public. The nonce-only
policy permits sk=10; the full policy rules out every recipe deducing that name. -/
theorem caller_policy_controls_name (swap : Bool) :
    MinimalRecipe names.nonceNames (world swap).value (.name 10) ∧
    ¬ (Term.name 10 : Recipe 3).Public names.restricted ∧
    ∀ r : Recipe 3, r.Public names.restricted → ¬ EqE ((world swap).eval r) (.name 10) := by
  refine ⟨MinimalRecipe.of_nodeCount_one (by change 10 ∉ names.nonceNames; decide) rfl,
    by change ¬ (10 ∉ names.restricted); decide, ?_⟩
  intro r hr
  exact frame_nonce_not_deducible names swap left right r hr (by decide : 10 ∈ names.restricted)

/-- Two unequal atomic minima instantiate the full swap branch in the actual
different-vote frames without a smaller-observation premise. Their exact values
also survive replacing every handle by another public name. -/
theorem minimum_atomic_step_inhabited :
    MinimalRecipe names.restricted (world false).value (.name 40) ∧
    MinimalRecipe names.restricted (world false).value (.const .zero) ∧
    ¬ EqE ((world false).eval (.name 40)) ((world false).eval (.const .zero)) ∧
    (EqE ((world false).eval (.name 40)) ((world false).eval (.const .zero)) ↔
      EqE ((world true).eval (.name 40)) ((world true).eval (.const .zero))) ∧
    (publishedAtom 41).eval (.name 40) = .name 40 ∧
    (publishedAtom 41).eval (.const .zero) = .const .zero := by
  obtain ⟨hr, hs⟩ := literal_atoms_minimum false 40 (by decide) .zero
  exact ⟨hr, hs, name_not_eqE_const 40 .zero,
    minimum_atomic_equality_swap names left right (.name 40) (.const .zero) hr hs
      (.name 40) (.const .zero) rfl rfl (.refl _) (.refl _),
    minimum_atomic_eval_any_frame names false left right names.restricted (.name 40) hr
      (.name 40) rfl (.refl _) (publishedAtom 41),
    minimum_atomic_eval_any_frame names false left right names.restricted (.const .zero) hs
      (.const .zero) rfl (.refl _) (publishedAtom 41)⟩

end ExplainableCrypto.Helios.Symbolic.AtomicObservationSPOT
