import ExplainableCrypto.Helios.Symbolic.NumericHandleAddition
import ExplainableCrypto.Helios.Symbolic.AdditionMinimumCosts

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Pure numeric syntax uses bits, marked numeric handles and addition only. -/
inductive NumericHandleExpression (ν : V → Option Nat) : Term V → Prop
  | zero : NumericHandleExpression ν (.const .zero)
  | one : NumericHandleExpression ν (.const .one)
  | handle (v : V) (number : Nat) : ν v = some number → NumericHandleExpression ν (.var v)
  | add {a b} : NumericHandleExpression ν a → NumericHandleExpression ν b →
      NumericHandleExpression ν (.binary .add a b)

/-- Numeric syntax introduces no public names and respects any caller policy. -/
theorem NumericHandleExpression.public {ν : V → Option Nat} {r : Term V}
    (h : NumericHandleExpression ν r) (restricted : Finset Nat) : r.Public restricted := by
  induction h with
  | zero | one | handle => trivial
  | add _ _ ia ib => exact ⟨ia,ib⟩

private theorem numeral_numeric (ν : V → Option Nat) (n : Nat) :
    NumericHandleExpression ν (addNumeral n) ∧
    (addNumeral n).addNumericSummary ν = AddSummary.number n := by
  induction n with
  | zero => exact ⟨.zero,rfl⟩
  | succ n ih => exact ⟨.add ih.1 .one,by simp only [addNumeral,Term.addNumericSummary,ih.2,AddSummary.combine_numbers]⟩

private theorem numeric_cost_exists (ν : V → Option Nat) (n : Nat) :
    ∃ k, ∃ r : Term V, NumericHandleExpression ν r ∧
      r.addNumericSummary ν = AddSummary.number n ∧ r.nodeCount+1 = k :=
  ⟨_,addNumeral n,(numeral_numeric ν n).1,(numeral_numeric ν n).2,rfl⟩

/-- Least node-count-plus-one for a present number using the available numeric
handles. Absence costs zero. This logical minimum does not assume a greedy
algorithm, literal-only costs or a decision procedure for full E. -/
noncomputable def numericHandleCost (ν : V → Option Nat) : Option Nat → Nat
  | none => 0
  | some n => by classical exact Nat.find (numeric_cost_exists ν n)

/-- Every present numeric cost is attained by public pure numeric syntax. -/
theorem numericHandleCost_realized (ν : V → Option Nat) (n : Nat) :
    ∃ r : Term V, NumericHandleExpression ν r ∧ r.addNumericSummary ν = AddSummary.number n ∧
      r.nodeCount+1 = numericHandleCost ν (some n) := by
  classical
  exact Nat.find_spec (numeric_cost_exists ν n)

/-- Any pure numeric expression pays at least the least attainable cost. -/
theorem numericHandleCost_le (ν : V → Option Nat) {r : Term V} {n : Nat}
    (hr : NumericHandleExpression ν r) (hs : r.addNumericSummary ν = AddSummary.number n) :
    numericHandleCost ν (some n) ≤ r.nodeCount+1 := by
  classical
  exact Nat.find_min' (numeric_cost_exists ν n) ⟨r,hr,hs,rfl⟩

/-- A present zero is not free: every present numeral needs at least one node. -/
theorem numericHandleCost_ge_two (ν : V → Option Nat) (n : Nat) :
    2 ≤ numericHandleCost ν (some n) := by
  obtain ⟨r,_,_,hc⟩ := numericHandleCost_realized ν n
  have := r.nodeCount_pos
  omega

/-- Both literal bits attain the smallest possible present numeric cost. -/
theorem numericHandleCost_bits (ν : V → Option Nat) :
    numericHandleCost ν (some 0) = 2 ∧ numericHandleCost ν (some 1) = 2 := by
  have hz := numericHandleCost_le ν (r := .const .zero) .zero rfl
  have ho := numericHandleCost_le ν (r := .const .one) .one rfl
  have := numericHandleCost_ge_two ν 0
  have := numericHandleCost_ge_two ν 1
  simp only [Term.nodeCount] at hz ho
  omega

/-- Every marked published numeral, including values above one, has cost two. -/
theorem numericHandleCost_handle (ν : V → Option Nat) (v : V) (n : Nat) (hn : ν v = some n) :
    numericHandleCost ν (some n) = 2 := by
  have h := numericHandleCost_le ν (n := n) (.handle v n hn) (by simp only [Term.addNumericSummary,hn])
  have := numericHandleCost_ge_two ν n
  simp only [Term.nodeCount] at h
  omega

/-- Combining realizers gives a valid cost upper bound, preserving numeric
presence. The least realizer may be strictly shorter than this combination. -/
theorem numericHandleCost_combine_le (ν : V → Option Nat) (a b : Option Nat) :
    numericHandleCost ν (numericAdd a b) ≤ numericHandleCost ν a+numericHandleCost ν b := by
  cases a with
  | none => cases b <;> simp [numericAdd,numericHandleCost]
  | some n =>
    cases b with
    | none => simp [numericAdd,numericHandleCost]
    | some m =>
      obtain ⟨r,hr,hs,hc⟩ := numericHandleCost_realized ν n
      obtain ⟨s,ht,hu,hd⟩ := numericHandleCost_realized ν m
      have hh := numericHandleCost_le ν (n := n+m) (.add hr ht)
        (by simp only [Term.addNumericSummary,hs,hu,AddSummary.combine_numbers])
      simp only [Term.nodeCount] at hh
      change numericHandleCost ν (some (n+m)) ≤ _
      omega

/-- Exact atom-occurrence costs plus the least attainable numeric cost. -/
noncomputable def AddSummary.numericHandleRecipeCost (ν : V → Option Nat) (s : AddSummary (Term V)) : Nat :=
  (s.atoms.map (fun a => a.nodeCount+1)).sum + numericHandleCost ν s.numeric

theorem AddSummary.numericHandleRecipeCost_combine_le (ν : V → Option Nat) (a b : AddSummary (Term V)) :
    (a.combine b).numericHandleRecipeCost ν ≤ a.numericHandleRecipeCost ν+b.numericHandleRecipeCost ν := by
  have h := numericHandleCost_combine_le ν a.numeric b.numeric
  simp only [numericHandleRecipeCost,combine,Multiset.map_add,Multiset.sum_add]
  omega

/-- Every raw recipe pays for its handle-aware summary. No semantic minimum
premise is needed for this syntactic lower bound. -/
theorem Term.addNumericSummary_cost_le (ν : V → Option Nat) (r : Term V) :
    (r.addNumericSummary ν).numericHandleRecipeCost ν ≤ r.nodeCount+1 := by
  induction r with
  | binary f a b ia ib =>
    cases f with
    | add =>
      have h := AddSummary.numericHandleRecipeCost_combine_le ν (a.addNumericSummary ν) (b.addNumericSummary ν)
      simp only [addNumericSummary,Term.nodeCount]
      omega
    | pair | mul | compose | partialDecrypt | dec =>
      simp [addNumericSummary,AddSummary.numericHandleRecipeCost,AddSummary.atom,numericHandleCost]
  | const c =>
    cases c with
    | zero => simp [addNumericSummary,AddSummary.numericHandleRecipeCost,AddSummary.number,(numericHandleCost_bits ν).1,Term.nodeCount]
    | one => simp [addNumericSummary,AddSummary.numericHandleRecipeCost,AddSummary.number,(numericHandleCost_bits ν).2,Term.nodeCount]
    | ok | bottom => simp [addNumericSummary,AddSummary.numericHandleRecipeCost,AddSummary.atom,numericHandleCost]
  | var v =>
    cases hn : ν v with
    | none => simp [addNumericSummary,hn,AddSummary.numericHandleRecipeCost,AddSummary.atom,numericHandleCost]
    | some n => simp [addNumericSummary,hn,AddSummary.numericHandleRecipeCost,AddSummary.number,numericHandleCost_handle ν v n hn,Term.nodeCount]
  | _ => simp [addNumericSummary,AddSummary.numericHandleRecipeCost,AddSummary.atom,numericHandleCost]

end ExplainableCrypto.Helios.Symbolic
