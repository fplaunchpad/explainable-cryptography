import ExplainableCrypto.Helios.Symbolic.ExpandedSingleMixedTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedPaddedExperiments
import ExplainableCrypto.Helios.Symbolic.ExpandedMixedSPOT

namespace ExplainableCrypto.Helios.Symbolic.ExpandedPaddedSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []
abbrev numbers (j : Fin 2) : Nat := j.val
abbrev table := expandedNumericHandles numbers
abbrev padded := ExpandedMixedSPOT.paddedPayload
abbrev duplicate : Recipe (ExpandedHandles 1) := .binary .add (.name 40) (.name 40)
private theorem public40 : (Term.name (V := Fin (ExpandedHandles 1)) 40).Public names.restricted := by
  change 40 ∉ names.restricted; decide
private theorem tally_numbers (swap : Bool) (j : Fin 2) : EqE (tallyResult names swap left right [] j) (addNumeral (numbers j)) := by
  fin_cases j
  · exact SharedTallySPOT.nonliteral_two_candidate_tally.1 swap
  · exact (SharedTallySPOT.nonliteral_two_candidate_tally.2 swap).trans (EqE.equation .zero_one).symm
private theorem numeric (swap : Bool) : ExpandedResultsNumeric names swap left right [] := fun j => ⟨numbers j,tally_numbers swap j⟩
private theorem padded_name (swap : Bool) : EqE ((world swap).eval (.binary .add padded (.const .zero)))
    ((world swap).eval (.binary .add (.name 40) (.const .zero))) := by
  apply padded_eqE_of_addNumericSummary _ table (expanded_numeric_handle_value names swap left right [] numbers (tally_numbers swap))
  · simp [Term.addNumericSummary,expanded_numeric_result,AddSummary.combine,AddSummary.atom,AddSummary.number]
  · simp [Term.addNumericSummary,expanded_numeric_result,AddSummary.combine,AddSummary.atom,AddSummary.number,numericAdd]

/-- The generic representative theorem removes a published zero from a
three-node payload, gives a one-node global padded minimum and preserves
padded values in both actual different-vote assignments. -/
theorem published_zero_padded_representative (swap swap' : Bool) :
    ∃ q, PaddedMinimalRecipe names.restricted (world swap).value q ∧ q.nodeCount=1 ∧
      EqE ((world swap).eval (.binary .add padded (.const .zero))) ((world swap).eval (.binary .add q (.const .zero))) ∧
      EqE ((world swap').eval (.binary .add padded (.const .zero))) ((world swap').eval (.binary .add q (.const .zero))) := by
  have hp := (ExpandedAddMinimumSPOT.zero_and_duplicate_global_minima swap).1
  obtain ⟨q,hq,ha,ht,_⟩ := expanded_padded_minimum_representative names swap left right [] numbers (tally_numbers swap)
    names.restricted padded hp.isPublic (fun a ha => hp.add_numeric_atom table ha)
  have he (s : Bool) := padded_eqE_of_addNumericSummary (world s).value table
    (expanded_numeric_handle_value names s left right [] numbers (tally_numbers s)) ha.symm ht.symm
  have hle := hq.2 (.name 40) public40 ((he swap).symm.trans (padded_name swap))
  have hpos := q.nodeCount_pos
  exact ⟨q,hq,by change q.nodeCount≤1 at hle; omega,he swap,he swap'⟩

/-- Empty and all-zero summaries have cost two, and a zero payload has one
real syntax node. Padding does not permit an empty recipe. -/
theorem zero_payload_is_nonempty (swap : Bool) :
    (AddSummary.empty : AddSummary (Recipe (ExpandedHandles 1))).paddedNumericHandleRecipeCost table=2 ∧
    (AddSummary.number 0 : AddSummary (Recipe (ExpandedHandles 1))).paddedNumericHandleRecipeCost table=2 ∧
    PaddedMinimalRecipe names.restricted (world swap).value (.const .zero) ∧
    ∀ r : Recipe (ExpandedHandles 1), 0<r.nodeCount := by
  refine ⟨?_,?_,⟨trivial,fun s _ _ => s.nodeCount_pos⟩,fun r => r.nodeCount_pos⟩
  all_goals simp [AddSummary.paddedNumericHandleRecipeCost,AddSummary.empty,AddSummary.number]

/-- Repeated atoms cost three nodes even under padded equality. Neither an
honest numeric message nor a published zero may erase an atom occurrence. -/
theorem duplicate_atoms_padded_minimum (swap : Bool) :
    PaddedMinimalRecipe names.restricted (world swap).value duplicate ∧ duplicate.nodeCount=3 ∧
    ¬ EqE ((world swap).eval (.binary .add duplicate (.const .zero)))
      ((world swap).eval (.binary .add (.name 40) (.const .zero))) := by
  have hm : PaddedMinimalRecipe names.restricted (world swap).value duplicate := by
    apply expanded_padded_minimum_of_exact_numeric_cost names swap left right [] numbers (tally_numbers swap)
      names.restricted duplicate ⟨public40,public40⟩
    · intro a ha
      have hh : a=.name 40 := by simpa [duplicate,Term.addNumericSummary,AddSummary.combine,AddSummary.atom] using ha
      subst a
      exact .of_nodeCount_one public40 rfl
    · simp [Term.nodeCount,Term.addNumericSummary,AddSummary.paddedNumericHandleRecipeCost,
        AddSummary.combine,AddSummary.atom,numericAdd]
  refine ⟨hm,rfl,?_⟩
  intro he
  have h := hm.2 (.name 40) public40 he
  change 3≤1 at h
  omega

/-- Published tally two has a one-node padded minimum; a literal two costs
three nodes. The initial literal-only padded cost would overestimate it. -/
theorem accepted_published_two_is_cheap (swap : Bool) :
    let φ := expandedFrame SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right SharedTallySPOT.submissions
    let ν := expandedNumericHandles (n := 0) (fun _ => 2)
    let r : Recipe (ExpandedHandles 0) := .var (expandedResult 0)
    EqE (φ.eval r) (addNumeral 2) ∧ PaddedMinimalRecipe SharedTallySPOT.names.restricted φ.value r ∧
      (r.addNumericSummary ν).paddedNumericHandleRecipeCost ν=2 ∧
      (Term.binary .add (.const .one) (.const .one) : Recipe (ExpandedHandles 0)).nodeCount=3 := by
  refine ⟨?_,⟨trivial,fun s _ _ => s.nodeCount_pos⟩,?_,rfl⟩
  · rw [Frame.eval,Term.subst,expanded_frame_result]
    exact (SharedTallySPOT.fresh_sequence_tally_two).1 swap
  · simp [Term.addNumericSummary,expanded_numeric_result,AddSummary.paddedNumericHandleRecipeCost,AddSummary.number,
      numericHandleCost_handle (expandedNumericHandles (n := 0) (fun _ => 2)) (expandedResult 0) 2 (expanded_numeric_result (fun _ => 2) 0)]

/-- Deleting a published zero is valid only after padding. Its unpadded
payload is a globally minimum three-node recipe and cannot equal one atom. -/
theorem unpadded_zero_deletion_refuted (swap : Bool) :
    EqE ((world swap).eval (.binary .add padded (.const .zero)))
      ((world swap).eval (.binary .add (.name 40) (.const .zero))) ∧
    ¬ EqE ((world swap).eval padded) ((world swap).eval (.name 40)) := by
  refine ⟨padded_name swap,?_⟩
  intro he
  exact (ExpandedAddMinimumSPOT.zero_and_duplicate_global_minima swap).1.no_smaller
    public40 he (by decide)

/-- Padded costs inherit the non-greedy optimum: two threes beat a four and
two ones, even with an additional nonnumeric atom in the payload. -/
theorem greedy_padded_cost_refuted :
    let ν : Nat → Option Nat := fun v => some (if v=0 then 3 else 4)
    (AddSummary.mk {Term.name 40} (some 6)).paddedNumericHandleRecipeCost ν=6 ∧
    (Term.binary .add (.name 40) (.binary .add (.var 1) (.binary .add (.const .one) (.const .one))) : Term Nat).nodeCount+1=8 := by
  have hc := ExpandedAddMinimumSPOT.greedy_choice_is_not_minimum.1
  simp [AddSummary.paddedNumericHandleRecipeCost,Term.nodeCount,hc]

private theorem short_minimum (swap : Bool) : MinimalRecipe names.restricted (world swap).value ExpandedMixedSPOT.singleShort :=
  expanded_minimum_mixed_of_minimum_components names HistoricalFrameSPOT.fixture_names_fresh swap left right []
    (by simp) (numeric swap) ExpandedMixedSPOT.trustee (.name 40) (.of_nodeCount_one trivial rfl)
      ⟨public40,fun s _ _ => s.nodeCount_pos⟩ ExpandedMixedSPOT.honest
private theorem mixed_value (swap : Bool) : EqE ((world swap).eval ExpandedMixedSPOT.singlePadded)
    ((world swap).eval ExpandedMixedSPOT.singleShort) := by
  have he := (expanded_group_ciphertext_eq_iff names HistoricalFrameSPOT.fixture_names_fresh swap left right [] (by simp)
    (.mixed ExpandedMixedSPOT.trustee padded ExpandedMixedSPOT.honest)
    (.mixed ExpandedMixedSPOT.trustee (.name 40) ExpandedMixedSPOT.honest)
    ⟨trivial,public40,trivial⟩ ⟨trivial,public40⟩ (publicKey names) (publicKey names)).mpr
    ⟨.refl _,rfl,.refl _,padded_name swap⟩
  exact (expanded_mixedCombination_value names swap left right [] _ _ _).trans
    (he.trans (expanded_mixedCombination_value names swap left right [] _ _ _).symm)

/-- The assembled all-multiplication theorem handles the formerly unresolved
one-constructor input. Reflexive smaller minima inhabit its induction premises;
the returned globally minimum representative has exactly seven nodes. -/
theorem all_multiplication_interface_closes_single_mixed (swap : Bool) :
    ∃ m, MinimalRecipe names.restricted (world swap).value m ∧
      EqE ((world swap).eval ExpandedMixedSPOT.singlePadded) ((world swap).eval m) ∧ m.nodeCount=7 ∧
      ¬ MinimalRecipe names.restricted (world swap).value ExpandedMixedSPOT.singlePadded := by
  have hchildren := (ExpandedMixedSPOT.one_constructor_payload_problem swap swap).1
  have hsmall : Frame.SharedMinimaBelow (world swap) (world swap) ExpandedMixedSPOT.singlePadded.nodeCount := by
    intro r hp _
    obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (world swap).value) r hp
    exact ⟨m,hm,he,he⟩
  obtain ⟨m,hm,he,_⟩ := accepted_expanded_minimum_children_mul_shared_of_two_way_minima names HistoricalFrameSPOT.fixture_names_fresh
    swap swap left right [] (by simp) trivial _ _ hchildren.1 hchildren.2 hsmall hsmall
  have hmin := short_minimum swap
  have heq := he.symm.trans (mixed_value swap)
  have h₁ := hm.least _ hmin.isPublic heq
  have h₂ := hmin.least m hm.isPublic heq.symm
  exact ⟨m,hm,he,by change m.nodeCount≤7 at h₁; change 7≤m.nodeCount at h₂; omega,
    (ExpandedMixedSPOT.one_constructor_payload_problem swap swap).2.1⟩

/-- The global mixed minimum closure accepts a genuinely non-atomic padded
payload with repeated atoms, producing a nine-node global mixed minimum. -/
theorem repeated_payload_mixed_minimum (swap swap' : Bool) :
    let r := mixedCombinationRecipeWith expandedOld ExpandedMixedSPOT.trustee duplicate ExpandedMixedSPOT.honest
    MinimalRecipe names.restricted (world swap).value r ∧ r.nodeCount=9 ∧
      Frame.SharedMinimum (world swap) (world swap') r := by
  have hm := expanded_minimum_mixed_of_minimum_components names HistoricalFrameSPOT.fixture_names_fresh swap left right []
    (by simp) (numeric swap) ExpandedMixedSPOT.trustee duplicate (.of_nodeCount_one trivial rfl)
      (duplicate_atoms_padded_minimum swap).1 ExpandedMixedSPOT.honest
  exact ⟨hm,rfl,.of_minimal hm⟩

end ExplainableCrypto.Helios.Symbolic.ExpandedPaddedSPOT
