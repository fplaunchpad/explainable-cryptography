import ExplainableCrypto.Helios.Symbolic.ExpandedAdditionTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedCompositionSPOT

namespace ExplainableCrypto.Helios.Symbolic.ExpandedAdditionSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []

private theorem small_observations (swap swap' : Bool) :
    (world swap).ObservationsBelow (world swap') 2 := by
  intro r s _ _ h
  have := r.nodeCount_pos
  have := s.nodeCount_pos
  omega

/-- The new equality branch applies to actual unequal honest voters. Comparing
the zero result with literal zero transfers and succeeds in either world. -/
theorem accepted_zero_handle_equality (swap swap' : Bool) :
    let r : Recipe (ExpandedHandles 1) := .var (expandedResult 0)
    let s : Recipe (ExpandedHandles 1) := .const .zero
    (EqE ((world swap).eval r) ((world swap).eval s) ↔
      EqE ((world swap').eval r) ((world swap').eval s)) ∧
    EqE ((world swap).eval r) ((world swap).eval s) := by
  have hz := SharedTallySPOT.nonliteral_two_candidate_tally.1 swap
  refine ⟨accepted_expanded_minimum_addition_equality_swap names HistoricalFrameSPOT.fixture_names_fresh
    swap swap' left right [] (by simp) trivial _ _ (.of_nodeCount_one trivial rfl)
    (.of_nodeCount_one trivial rfl) (hz.trans (EqE.equation .zero_zero).symm)
    (EqE.equation .zero_zero).symm (small_observations swap swap'),hz⟩

/-- The same branch preserves a failing equality test between different tally
slots, excluding constant-output and all-equalities-true explanations. -/
theorem accepted_distinct_result_equality (swap swap' : Bool) :
    let r : Recipe (ExpandedHandles 1) := .var (expandedResult 0)
    let s : Recipe (ExpandedHandles 1) := .var (expandedResult 1)
    (EqE ((world swap).eval r) ((world swap).eval s) ↔
      EqE ((world swap').eval r) ((world swap').eval s)) ∧
    ¬ EqE ((world swap).eval r) ((world swap).eval s) := by
  have hz := SharedTallySPOT.nonliteral_two_candidate_tally.1 swap
  have ho := SharedTallySPOT.nonliteral_two_candidate_tally.2 swap
  refine ⟨accepted_expanded_minimum_addition_equality_swap names HistoricalFrameSPOT.fixture_names_fresh
    swap swap' left right [] (by simp) trivial _ _ (.of_nodeCount_one trivial rfl)
    (.of_nodeCount_one trivial rfl) (hz.trans (EqE.equation .zero_zero).symm)
    (ho.trans (EqE.equation .zero_one).symm) (small_observations swap swap'),?_⟩
  intro he
  exact zero_not_one (hz.symm.trans (he.trans ho))

/-- Mixed additive values exercise the atom branch on minimum representatives.
The two original expressions have repeated public names and a published numeral;
commutativity supplies their independently derived equality. -/
theorem accepted_mixed_minimum_comparison :
    let φ := expandedFrame names false left left []
    let ψ := expandedFrame names true left left []
    let a : Recipe (ExpandedHandles 1) := .name 40
    let b : Recipe (ExpandedHandles 1) := .var (expandedResult 1)
    let r := Term.binary .add a (.binary .add b a)
    let s := Term.binary .add (.binary .add a b) a
    ∃ m k, MinimalRecipe names.restricted φ.value m ∧ MinimalRecipe names.restricted φ.value k ∧
      EqE (φ.eval m) (φ.eval r) ∧ EqE (φ.eval k) (φ.eval s) ∧
      (EqE (φ.eval m) (φ.eval k) ↔ EqE (ψ.eval m) (ψ.eval k)) ∧ EqE (φ.eval m) (φ.eval k) := by
  let φ := expandedFrame names false left left []
  let a : Recipe (ExpandedHandles 1) := .name 40
  let b : Recipe (ExpandedHandles 1) := .var (expandedResult 1)
  let r := Term.binary .add a (.binary .add b a)
  let s := Term.binary .add (.binary .add a b) a
  have hap : a.Public names.restricted := by change 40 ∉ names.restricted; decide
  obtain ⟨m,hm,hem⟩ := exists_minimal_recipe (σ := φ.value) r ⟨hap,trivial,hap⟩
  obtain ⟨k,hk,hek⟩ := exists_minimal_recipe (σ := φ.value) s ⟨⟨hap,trivial⟩,hap⟩
  have hrs : EqE (φ.eval r) (φ.eval s) :=
    (EqE.equation (.comm .add trivial _ _)).trans
      (EqE.binary .add (.equation (.comm .add trivial _ _)) (.refl _))
  exact ⟨m,k,hm,hk,hem.symm,hek.symm,
    accepted_expanded_minimum_addition_equality_swap names HistoricalFrameSPOT.fixture_names_fresh
      false true left left [] (by simp) trivial m k hm hk hem.symm hek.symm (fun _ _ _ _ _ => Iff.rfl),
    hem.symm.trans (hrs.trans hek)⟩

/-- An accepted tally of two is available at size one. The literal numeric
cost inequality is false, and the original three syntax origins are incomplete. -/
theorem published_two_refutes_literal_cost (swap : Bool) :
    let φ := expandedFrame SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right SharedTallySPOT.submissions
    let r : Recipe (ExpandedHandles 0) := .var (expandedResult 0)
    MinimalRecipe SharedTallySPOT.names.restricted φ.value r ∧
    EqE (φ.eval r) (addNumeral 2) ∧ ExpandedAdditionRecipeForm r ∧
    ¬ ((∃ a b, r = .binary .add a b) ∨ r = .const .zero ∨ r = .const .one) ∧
    ¬ (numericRecipeCost (some 2) ≤ r.nodeCount+1) := by
  refine ⟨.of_nodeCount_one trivial rfl, SharedTallySPOT.fresh_sequence_tally_two.1 swap,
    Or.inr ⟨0,rfl⟩,?_,by decide⟩
  rintro (⟨a,b,h⟩ | h | h) <;> cases h

/-- A numeric handle is expanded to a numeral, although its raw decryption
syntax would contribute an atom to an unexpanded addition summary. -/
theorem result_summary_requires_numeric_expansion (swap : Bool) :
    let r : Recipe (ExpandedHandles 1) := .var (expandedResult 0)
    r.addSyntaxSummary = AddSummary.atom r ∧
    r.addNumericSummary (expandedNumericHandles (fun j : Fin 2 => j.val)) = AddSummary.number 0 ∧
    EqE ((world swap).eval r)
      (r.addNumericValue (world swap).value (expandedNumericHandles (fun j : Fin 2 => j.val))) := by
  refine ⟨rfl,by decide,?_⟩
  exact SharedTallySPOT.nonliteral_two_candidate_tally.1 swap

/-- Adding a published zero to a name retains numeric presence under full E;
zero is not a global additive unit. -/
theorem published_zero_is_present (swap : Bool) :
    let r : Recipe (ExpandedHandles 1) := .binary .add (.name 40) (.var (expandedResult 0))
    (r.addNumericSummary (expandedNumericHandles (fun j : Fin 2 => j.val))).numeric = some 0 ∧
    ¬ EqE ((world swap).eval r) (.name 40) := by
  refine ⟨by decide,?_⟩
  intro he
  have hv : EqE ((world swap).eval (.binary .add (.name 40) (.var (expandedResult 0))))
      (.binary .add (.name 40) (.const .zero)) :=
    EqE.binary .add (.refl _) (SharedTallySPOT.nonliteral_two_candidate_tally.1 swap)
  exact arithmetic_not_eqE_name .add (Or.inl rfl) _ _ 40 (hv.symm.trans he)

/-- Repeated published ones add to two; repeated nonnumeric leaves remain two
occurrences. The independently expected numeric count is not saturated. -/
theorem repeated_slots_and_atoms :
    let z : Recipe (ExpandedHandles 1) := .var (expandedResult 0)
    let o : Recipe (ExpandedHandles 1) := .var (expandedResult 1)
    let r := Term.binary .add (.name 40) (.binary .add z (.binary .add o (.binary .add (.name 40) o)))
    r.addNumericSummary (expandedNumericHandles (fun j : Fin 2 => j.val)) =
      AddSummary.mk {.name 40,.name 40} (some 2) := by decide

/-- Addition of minimum children need not be minimum. Two actual published
numeric handles can collapse to the one-valued result handle. -/
theorem numeric_children_do_not_give_minimum_closure (swap : Bool) :
    let z : Recipe (ExpandedHandles 1) := .var (expandedResult 0)
    let o : Recipe (ExpandedHandles 1) := .var (expandedResult 1)
    MinimalRecipe names.restricted (world swap).value z ∧
    MinimalRecipe names.restricted (world swap).value o ∧
    EqE ((world swap).eval (.binary .add z o)) ((world swap).eval o) ∧
    ¬ MinimalRecipe names.restricted (world swap).value (.binary .add z o) := by
  have he : EqE ((world swap).eval (.binary .add (.var (expandedResult 0)) (.var (expandedResult 1))))
      ((world swap).eval (.var (expandedResult 1))) :=
    (EqE.binary .add (SharedTallySPOT.nonliteral_two_candidate_tally.1 swap)
      (SharedTallySPOT.nonliteral_two_candidate_tally.2 swap)).trans
      ((EqE.equation .zero_one).trans (SharedTallySPOT.nonliteral_two_candidate_tally.2 swap).symm)
  refine ⟨.of_nodeCount_one trivial rfl,.of_nodeCount_one trivial rfl,he,?_⟩
  intro hm
  have h := hm.least (.var (expandedResult 1)) trivial he
  change 3 ≤ 1 at h
  omega

/-- Successful projection and E5 decryption can expose additive values from
other raw heads; both wrappers are excluded precisely by source minimality. -/
theorem hidden_addition_wrappers_nonminimum (swap : Bool) :
    let a : Recipe (ExpandedHandles 1) := .binary .add (.name 40) (.var (expandedResult 1))
    let p := Term.unary .fst (.binary .pair a (.name 50))
    let key : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
    let d := Term.binary .dec key (keyCiphertext key (.name 50) a)
    EqE ((world swap).eval p) ((world swap).eval a) ∧
    EqE ((world swap).eval d) ((world swap).eval a) ∧
    ¬ MinimalRecipe names.restricted (world swap).value p ∧
    ¬ MinimalRecipe names.restricted (world swap).value d := by
  refine ⟨.equation (.fst _ _),(RootStep.decrypt _ _ _).sound,?_,?_⟩
  · intro hm
    exact hm.raw_irreducible _ (RootStep.fst _ _).to_rewrite
  · intro hm
    exact hm.raw_irreducible _ (RootStep.decrypt _ _ _).to_rewrite

/-- Real E6 success remains enabled and yields an additive numeral. Destination
origin arguments therefore need the explicit published-result probe. -/
theorem E6_output_is_additive (swap : Bool) :
    (∃ out, DecryptionMatch (tallyPartial names swap left right [] 1) (tallyCiphertext names swap left right [] 1) out) ∧
    EqE (tallyResult names swap left right [] 1) (.binary .add (.const .zero) (.const .one)) :=
  ⟨(TrusteePartialSPOT.both_candidates_match swap 1).1,
    (SharedTallySPOT.nonliteral_two_candidate_tally.2 swap).trans (EqE.equation .zero_one).symm⟩

end ExplainableCrypto.Helios.Symbolic.ExpandedAdditionSPOT
