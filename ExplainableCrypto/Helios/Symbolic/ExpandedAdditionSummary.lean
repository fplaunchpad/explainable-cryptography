import ExplainableCrypto.Helios.Symbolic.ExpandedAdditionOrigins
import ExplainableCrypto.Helios.Symbolic.NumericHandleAddition
import ExplainableCrypto.Helios.Symbolic.AdditionObservationInduction

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- The numeric contribution of each published result; old and partial handles
remain eligible nonnumeric leaves. -/
def expandedNumericHandles (numbers : Fin (n+1) → Nat) : Fin (ExpandedHandles n) → Option Nat :=
  Fin.addCases (fun _ => none) (Fin.addCases (fun _ => none) (fun j => some (numbers j)))

@[simp]
theorem expanded_numeric_result (numbers : Fin (n+1) → Nat) (j : Fin (n+1)) :
    expandedNumericHandles numbers (expandedResult j) = some (numbers j) := by
  simp only [expandedNumericHandles,expandedResult,Fin.addCases_right]

/-- Known tally numbers justify every handle expansion in the semantic summary. -/
theorem expanded_numeric_handle_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (numbers : Fin (n+1) → Nat)
    (hn : ∀ j, EqE (tallyResult ns swap left right rs j) (addNumeral (numbers j)))
    (v : Fin (ExpandedHandles n)) (number : Nat)
    (hv : expandedNumericHandles numbers v = some number) :
    EqE ((expandedFrame ns swap left right rs).value v) (addNumeral number) := by
  revert hv
  refine Fin.addCases (fun old => ?_) (fun extra => ?_) v
  · simp [expandedNumericHandles]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) extra
    · simp [expandedNumericHandles]
    · intro hv
      have hh : numbers j = number := by simpa only [expandedNumericHandles,Fin.addCases_right,Option.some.injEq] using hv
      subst number
      simpa only [expandedFrame,Fin.addCases_right] using hn j

/-- Every nonnumeric leaf of an additive recipe is strictly smaller, even when
the entire recipe is a size-one result handle with no atom leaves. -/
theorem expanded_add_numeric_leaf_smaller (numbers : Fin (n+1) → Nat)
    {r leaf : Recipe (ExpandedHandles n)} (hr : ExpandedAdditionRecipeForm r)
    (h : leaf ∈ (r.addNumericSummary (expandedNumericHandles numbers)).atoms) :
    leaf.nodeCount < r.nodeCount := by
  rcases hr with (⟨a,b,rfl⟩ | rfl | rfl) | ⟨j,rfl⟩
  · rcases Multiset.mem_add.mp h with ha | hb
    · obtain ⟨⟨c,hc⟩,_⟩ := Term.addNumericSummary_mem _ ha
      have hle := c.nodeCount_hole_le leaf
      rw [hc] at hle
      simp only [Term.nodeCount]
      omega
    · obtain ⟨⟨c,hc⟩,_⟩ := Term.addNumericSummary_mem _ hb
      have hle := c.nodeCount_hole_le leaf
      rw [hc] at hle
      simp only [Term.nodeCount]
      omega
  · exact False.elim (Multiset.notMem_zero leaf h)
  · exact False.elim (Multiset.notMem_zero leaf h)
  · simp [Term.addNumericSummary,AddSummary.number] at h

/-- Smaller leaves pay for the result probe needed by destination addition
origins. The bound remains the original pair's size sum. -/
theorem accepted_expanded_minimum_add_numeric_leaf_values (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (numbers : Fin (n+1) → Nat) (r s : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (hr : ExpandedAdditionRecipeForm r)
    (hobs : (expandedFrame ns swap left right rs).ObservationsBelow
      (expandedFrame ns swap' left right rs) (r.nodeCount+s.nodeCount)) :
    (∀ a ∈ (r.addNumericSummary (expandedNumericHandles numbers)).atoms,
      ((expandedFrame ns swap left right rs).eval a).fullClass.AddAtom) ∧
    (∀ a ∈ (r.addNumericSummary (expandedNumericHandles numbers)).atoms,
      ((expandedFrame ns swap' left right rs).eval a).fullClass.AddAtom) := by
  have info {a : Recipe (ExpandedHandles n)}
      (hleaf : a ∈ (r.addNumericSummary (expandedNumericHandles numbers)).atoms) :
      MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value a ∧
      a.nodeCount+2 ≤ r.nodeCount+s.nodeCount ∧ ¬ ExpandedAdditionRecipeForm a := by
    obtain ⟨⟨c,hc⟩,hadd,hz,ho,hv⟩ := Term.addNumericSummary_mem _ hleaf
    have hmc := hm
    rw [← hc] at hmc
    refine ⟨hmc.subterm c,?_,?_⟩
    · have := expanded_add_numeric_leaf_smaller numbers hr hleaf
      have := s.nodeCount_pos
      omega
    · rintro ((⟨x,y,he⟩ | he | he) | ⟨j,he⟩)
      · exact hadd x y he
      · exact hz he
      · exact ho he
      · have hh := hv _ he
        simp at hh
  have atom_of_no_add {t : Ground} (h : ∀ x y, ¬ EqE t (.binary .add x y)) : t.fullClass.AddAtom := by
    refine ⟨fun x y he => h x y ((fullClass_eq_iff _ _).mp he), ?_, ?_⟩
    · intro he
      exact h _ _ (((fullClass_eq_iff _ _).mp he).trans (EqE.equation .zero_zero).symm)
    · intro he
      exact h _ _ (((fullClass_eq_iff _ _).mp he).trans (EqE.equation .zero_one).symm)
  constructor
  · intro a hleaf
    have hi := info hleaf
    exact atom_of_no_add (fun x y he => hi.2.2 (expanded_minimum_add_form ns swap left right rs
      (accepted_expanded_results_numeric ns hf left right rs hp ha swap) ns.restricted a hi.1 he))
  · intro a hleaf
    have hi := info hleaf
    exact atom_of_no_add (fun x y he => hi.2.2 (accepted_expanded_minimum_add_form_after_swap ns hf
      swap swap' left right rs hp ha a hi.1 (hobs.mono hi.2.1) he))

/-- A shared numeric-handle table leaves only smaller public atom comparisons
in summary equality. Multiplicity and optional numeric presence are retained. -/
theorem expanded_add_numeric_summary_transfer (numbers : Fin (n+1) → Nat)
    {restricted : Finset Nat} (φ ψ : Frame restricted (ExpandedHandles n))
    (r s : Recipe (ExpandedHandles n)) (hp : r.Public restricted) (hq : s.Public restricted)
    (hr : ExpandedAdditionRecipeForm r) (hs : ExpandedAdditionRecipeForm s)
    (hobs : φ.ObservationsBelow ψ (r.nodeCount+s.nodeCount)) :
    (AddSummary.mk ((r.addNumericSummary (expandedNumericHandles numbers)).atoms.map (fun a => (φ.eval a).fullClass))
      (r.addNumericSummary (expandedNumericHandles numbers)).numeric =
      AddSummary.mk ((s.addNumericSummary (expandedNumericHandles numbers)).atoms.map (fun a => (φ.eval a).fullClass))
      (s.addNumericSummary (expandedNumericHandles numbers)).numeric) ↔
    (AddSummary.mk ((r.addNumericSummary (expandedNumericHandles numbers)).atoms.map (fun a => (ψ.eval a).fullClass))
      (r.addNumericSummary (expandedNumericHandles numbers)).numeric =
      AddSummary.mk ((s.addNumericSummary (expandedNumericHandles numbers)).atoms.map (fun a => (ψ.eval a).fullClass))
      (s.addNumericSummary (expandedNumericHandles numbers)).numeric) := by
  simp only [AddSummary.mk.injEq]
  apply and_congr_left
  intro _
  apply multiset_mapped_equality_transfer
  intro x hx y hy
  obtain ⟨⟨cx,hcx⟩,_⟩ := Term.addNumericSummary_mem _ hx
  obtain ⟨⟨cy,hcy⟩,_⟩ := Term.addNumericSummary_mem _ hy
  have hpx : x.Public restricted := cx.public_hole (by simpa only [hcx] using hp)
  have hpy : y.Public restricted := cy.public_hole (by simpa only [hcy] using hq)
  have hsx := expanded_add_numeric_leaf_smaller numbers hr hx
  have hsy := expanded_add_numeric_leaf_smaller numbers hs hy
  exact (fullClass_eq_iff _ _).trans ((hobs x y hpx hpy (by omega)).trans (fullClass_eq_iff _ _).symm)

end ExplainableCrypto.Helios.Symbolic.Historical.General
