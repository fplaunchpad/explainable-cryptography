import ExplainableCrypto.Helios.Symbolic.ExpandedAddMinimumClosure
import ExplainableCrypto.Helios.Symbolic.ExpandedAdditionSPOT
import ExplainableCrypto.Helios.Symbolic.ExpandedAddMinimumExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedAddMinimumSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []
abbrev numbers (j : Fin 2) : Nat := j.val
abbrev table := expandedNumericHandles numbers

private theorem tally_numbers (swap : Bool) (j : Fin 2) :
    EqE (tallyResult names swap left right [] j) (addNumeral (numbers j)) := by
  fin_cases j
  · exact SharedTallySPOT.nonliteral_two_candidate_tally.1 swap
  · exact (SharedTallySPOT.nonliteral_two_candidate_tally.2 swap).trans (EqE.equation .zero_one).symm

/-- The general theorem shares a minimum for the collapsing sum of actual
published zero/one slots, although the original sum is not itself minimum. -/
theorem collapsed_numeric_sum_shared (swap swap' : Bool) :
    let z : Recipe (ExpandedHandles 1) := .var (expandedResult 0)
    let o : Recipe (ExpandedHandles 1) := .var (expandedResult 1)
    Frame.SharedMinimum (world swap) (world swap') (.binary .add z o) ∧
    ¬ MinimalRecipe names.restricted (world swap).value (.binary .add z o) :=
  ⟨accepted_expanded_minimum_children_add_shared names HistoricalFrameSPOT.fixture_names_fresh
    swap swap' left right [] (by simp) trivial _ _ (.of_nodeCount_one trivial rfl) (.of_nodeCount_one trivial rfl),
    (ExpandedAdditionSPOT.numeric_children_do_not_give_minimum_closure swap).2.2.2⟩

/-- A mixed public-name/result sum has a shared minimum for genuinely different
honest voters, with no smaller-observation premise. -/
theorem mixed_sum_shared (swap swap' : Bool) :
    Frame.SharedMinimum (world swap) (world swap') (.binary .add (.name 40) (.var (expandedResult 1))) :=
  accepted_expanded_minimum_children_add_shared names HistoricalFrameSPOT.fixture_names_fresh
    swap swap' left right [] (by simp) trivial _ _
    (.of_nodeCount_one (by change 40 ∉ names.restricted; decide) rfl) (.of_nodeCount_one trivial rfl)

/-- Exact cost gives global three-node minima for a name plus published zero
and for two repeated names. Numeric presence and multiplicity cannot disappear. -/
theorem zero_and_duplicate_global_minima (swap : Bool) :
    MinimalRecipe names.restricted (world swap).value (.binary .add (.name 40) (.var (expandedResult 0))) ∧
    MinimalRecipe names.restricted (world swap).value (.binary .add (.name 40) (.name 40)) := by
  have hp : (Term.name (V := Fin (ExpandedHandles 1)) 40).Public names.restricted := by change 40 ∉ names.restricted; decide
  have hm : MinimalRecipe names.restricted (world swap).value (.name 40) := .of_nodeCount_one hp rfl
  constructor
  · apply expanded_minimum_add_of_exact_numeric_cost names swap left right [] numbers (tally_numbers swap)
      names.restricted (.binary .add (.name 40) (.var (expandedResult 0))) ⟨hp,trivial⟩
    · intro a ha
      simp [Term.addNumericSummary,expanded_numeric_result,AddSummary.combine,AddSummary.atom,AddSummary.number] at ha
      subst a
      exact hm
    · simp [Term.nodeCount,Term.addNumericSummary,expanded_numeric_result,AddSummary.numericHandleRecipeCost,
        AddSummary.combine,AddSummary.atom,AddSummary.number,numericAdd,(numericHandleCost_bits table).1]
  · apply expanded_minimum_add_of_exact_numeric_cost names swap left right [] numbers (tally_numbers swap)
      names.restricted (.binary .add (.name 40) (.name 40)) ⟨hp,hp⟩
    · intro a ha
      simp [Term.addNumericSummary,AddSummary.combine,AddSummary.atom] at ha
      subst a
      exact hm
    · simp [Term.nodeCount,Term.addNumericSummary,AddSummary.numericHandleRecipeCost,
        AddSummary.combine,AddSummary.atom,numericAdd,numericHandleCost]

/-- A nonnumeric atom that merely attains its raw cost can still hide a shorter
projection value. Global minimality requires minimum atom leaves. -/
theorem nonminimum_atom_breaks_cost_criterion (swap : Bool) :
    let a : Recipe (ExpandedHandles 1) := .unary .fst (.binary .pair (.name 40) (.const .bottom))
    let r := Term.binary .add a (.var (expandedResult 1))
    r.nodeCount+1 = (r.addNumericSummary table).numericHandleRecipeCost table ∧
    ¬ MinimalRecipe names.restricted (world swap).value r := by
  constructor
  · simp [Term.nodeCount,Term.addNumericSummary,table,expanded_numeric_result,AddSummary.numericHandleRecipeCost,
      AddSummary.combine,AddSummary.atom,AddSummary.number,numericAdd,(numericHandleCost_bits table).2]
  · intro hm
    exact hm.no_smaller (s := .binary .add (.name 40) (.var (expandedResult 1)))
      ⟨by change 40 ∉ names.restricted; decide,trivial⟩
      (EqE.binary .add (.equation (.fst _ _)) (.refl _)) (by decide)

/-- Actual accepted result two is a one-node global minimum. Its numeric cost
is two rather than the literal-only cost four. -/
theorem accepted_two_is_cheap (swap : Bool) :
    let φ := expandedFrame SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right SharedTallySPOT.submissions
    let ν := expandedNumericHandles (fun _ : Fin 1 => 2)
    let r : Recipe (ExpandedHandles 0) := .var (expandedResult 0)
    MinimalRecipe SharedTallySPOT.names.restricted φ.value r ∧ EqE (φ.eval r) (addNumeral 2) ∧
    numericHandleCost ν (some 2) = 2 ∧ numericRecipeCost (some 2) = 4 :=
  ⟨.of_nodeCount_one trivial rfl,SharedTallySPOT.fresh_sequence_tally_two.1 swap,
    numericHandleCost_handle _ (expandedResult 0) 2 (expanded_numeric_result _ 0),rfl⟩

/-- A present zero needs one node; absence contributes no numeric cost. The
same distinction holds for every arbitrary numeric-handle table. -/
theorem zero_presence_cost (ν : Fin 3 → Option Nat) :
    numericHandleCost ν none = 0 ∧ numericHandleCost ν (some 0) = 2 :=
  ⟨rfl,(numericHandleCost_bits ν).1⟩

/-- The least realizer finds 3+3 for target six with published values three and
four. Greedy 4+1+1 has higher cost; the finite oracle agrees on this witness. -/
theorem greedy_choice_is_not_minimum :
    let ν : Nat → Option Nat := fun v => some (if v = 0 then 3 else 4)
    numericHandleCost ν (some 6) = 4 ∧
    (Term.binary .add (.var 1) (.binary .add (.const .one) (.const .one)) : Term Nat).nodeCount+1 = 6 ∧
    ExpandedAddMinimumExperiments.coinCount 3 4 6 = 2 := by
  let ν : Nat → Option Nat := fun v => some (if v = 0 then 3 else 4)
  have hu := numericHandleCost_le ν (n := 6) (.add (.handle 0 3 rfl) (.handle 0 3 rfl)) (by decide)
  obtain ⟨r,hr,hs,hc⟩ := numericHandleCost_realized ν 6
  have hl : 4 ≤ r.nodeCount+1 := by
    cases hr with
    | zero | one => have hh := congrArg AddSummary.numeric hs; cases hh
    | handle v number hv =>
      have hh := congrArg AddSummary.numeric hs
      simp only [Term.addNumericSummary,hv,AddSummary.number] at hh
      have hnumber : number = 6 := Option.some.inj hh
      subst number
      simp only [ν,Option.some.injEq] at hv
      split at hv <;> omega
    | @add a b ha hb =>
      have := a.nodeCount_pos
      have := b.nodeCount_pos
      simp only [Term.nodeCount]
      omega
  refine ⟨?_,rfl,by decide⟩
  simp only [Term.nodeCount] at hu
  exact Nat.le_antisymm hu (hc ▸ hl)

/-- A summary table alone cannot justify equality in an unrelated destination
frame. The shared numeric-value premise prevents this false transport. -/
theorem shared_numeric_values_required :
    let φ : Frame ∅ 1 := ⟨fun _ => .const .zero⟩
    let ψ : Frame ∅ 1 := ⟨fun _ => .const .one⟩
    let ν : Fin 1 → Option Nat := fun _ => some 0
    let r : Recipe 1 := .var 0
    let s : Recipe 1 := .const .zero
    r.addNumericSummary ν = s.addNumericSummary ν ∧ EqE (φ.eval r) (φ.eval s) ∧
    ¬ EqE (ψ.eval r) (ψ.eval s) :=
  ⟨rfl,.refl _,fun he => zero_not_one he.symm⟩

end ExplainableCrypto.Helios.Symbolic.ExpandedAddMinimumSPOT
