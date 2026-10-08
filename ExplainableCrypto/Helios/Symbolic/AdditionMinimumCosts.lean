import ExplainableCrypto.Helios.Symbolic.DecryptCheckAddMulTransport

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type} {restricted : Finset Nat} {σ : V → Term W}

/-- Numeric contribution to node count plus one: absent costs zero, a present
zero costs two, and a positive count n costs two per retained one. -/
def numericRecipeCost : Option Nat → Nat
  | none => 0
  | some n => 2 * max 1 n

def AddSummary.recipeCost (s : AddSummary (Term V)) : Nat :=
  (s.atoms.map (fun a => a.nodeCount+1)).sum + numericRecipeCost s.numeric

theorem numericRecipeCost_combine_le (a b : Option Nat) :
    numericRecipeCost (numericAdd a b) ≤ numericRecipeCost a + numericRecipeCost b := by
  cases a <;> cases b <;> simp only [numericAdd,numericRecipeCost] <;> omega

theorem AddSummary.recipeCost_combine_le (a b : AddSummary (Term V)) :
    (a.combine b).recipeCost ≤ a.recipeCost + b.recipeCost := by
  have h := numericRecipeCost_combine_le a.numeric b.numeric
  simp only [recipeCost,combine,Multiset.map_add,Multiset.sum_add]
  omega

/-- Every raw recipe pays at least its atom costs and normalized numeric cost. -/
theorem Term.addSyntaxSummary_cost_le (r : Term V) : r.addSyntaxSummary.recipeCost ≤ r.nodeCount+1 := by
  induction r with
  | binary f a b ia ib =>
    cases f with
    | add =>
      have h := AddSummary.recipeCost_combine_le a.addSyntaxSummary b.addSyntaxSummary
      simp only [addSyntaxSummary,Term.nodeCount]
      omega
    | pair | mul | compose | partialDecrypt | dec =>
      simp [addSyntaxSummary,AddSummary.recipeCost,AddSummary.atom,numericRecipeCost]
  | const c => cases c <;> simp [addSyntaxSummary,AddSummary.recipeCost,AddSummary.atom,AddSummary.number,numericRecipeCost,Term.nodeCount]
  | _ => simp [addSyntaxSummary,AddSummary.recipeCost,AddSummary.atom,numericRecipeCost]

/-- The raw syntax summary maps to the existing complete E0 summary. -/
theorem Term.addSummary_from_syntax (r : Term V) :
    r.addSummary = ⟨r.addSyntaxSummary.atoms.map Term.baseClass,r.addSyntaxSummary.numeric⟩ := by
  induction r with
  | binary f a b ia ib =>
    cases f <;> simp_all [addSummary,addSyntaxSummary,AddSummary.combine,AddSummary.atom,Multiset.map_add]
  | const c => cases c <;> simp [addSummary,addSyntaxSummary,AddSummary.atom,AddSummary.number]
  | _ => simp [addSummary,addSyntaxSummary,AddSummary.atom]

theorem baseEq_of_addSyntaxSummary_eq {r s : Term V} (he : r.addSyntaxSummary = s.addSyntaxSummary) :
    BaseEq r s := by
  apply (baseEq_iff_addSummary r s).mpr
  rw [r.addSummary_from_syntax,s.addSummary_from_syntax,he]

theorem Term.addSyntaxSummary_ne_empty (r : Term V) : r.addSyntaxSummary ≠ .empty := by
  intro he
  have h := r.addSummary_ne_empty
  rw [r.addSummary_from_syntax,he] at h
  exact h (by simp [AddSummary.empty])

theorem Term.addSyntaxSummary_atom {r : Term V} (ha : ∀ a b, r ≠ .binary .add a b)
    (hz : r ≠ .const .zero) (ho : r ≠ .const .one) : r.addSyntaxSummary = .atom r := by
  cases r with
  | binary f a b => cases f <;> first | rfl | exact False.elim (ha a b rfl)
  | const c => cases c <;> first | rfl | exact False.elim (hz rfl) | exact False.elim (ho rfl)
  | _ => rfl

theorem MinimalRecipe.add_atom {r a : Term V} (hm : MinimalRecipe restricted σ r)
    (ha : a ∈ r.addSyntaxSummary.atoms) : MinimalRecipe restricted σ a := by
  obtain ⟨⟨c,hc⟩,_⟩ := Term.addSyntaxSummary_mem ha
  rw [← hc] at hm
  exact hm.subterm c

end ExplainableCrypto.Helios.Symbolic
