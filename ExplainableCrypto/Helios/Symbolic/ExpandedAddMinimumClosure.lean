import ExplainableCrypto.Helios.Symbolic.NumericHandleRealization
import ExplainableCrypto.Helios.Symbolic.ExpandedAdditionTransport

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type} {restricted : Finset Nat} {σ : V → Term W}

/-- Minimum recipes pass their global minimum property to every numeric-aware
nonnumeric atom occurrence. -/
theorem MinimalRecipe.add_numeric_atom (ν : V → Option Nat) {r a : Term V}
    (hm : MinimalRecipe restricted σ r) (ha : a ∈ (r.addNumericSummary ν).atoms) :
    MinimalRecipe restricted σ a := by
  obtain ⟨⟨c,hc⟩,_⟩ := Term.addNumericSummary_mem ν ha
  rw [← hc] at hm
  exact hm.subterm c

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Source-minimum nonnumeric leaves remain semantic addition atoms. Every
result handle is excluded by the numeric-aware syntax summary. -/
theorem expanded_minimum_add_numeric_atoms_atomic (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (numbers : Fin (n+1) → Nat)
    (restricted : Finset Nat) (r : Recipe (ExpandedHandles n))
    (hmin : ∀ a ∈ (r.addNumericSummary (expandedNumericHandles numbers)).atoms,
      MinimalRecipe restricted (expandedFrame ns swap left right rs).value a) :
    ∀ a ∈ (r.addNumericSummary (expandedNumericHandles numbers)).atoms,
      ((expandedFrame ns swap left right rs).eval a).fullClass.AddAtom := by
  intro a ha
  obtain ⟨_,hadd,hz,ho,hv⟩ := Term.addNumericSummary_mem _ ha
  have noadd : ∀ x y, ¬ EqE ((expandedFrame ns swap left right rs).eval a) (.binary .add x y) := by
    intro x y he
    rcases expanded_minimum_add_form ns swap left right rs hn restricted a (hmin a ha) he with
      (⟨u,v,h⟩ | h | h) | ⟨j,h⟩
    · exact hadd u v h
    · exact hz h
    · exact ho h
    · have hh := hv _ h
      simp at hh
  refine ⟨fun x y he => noadd x y ((fullClass_eq_iff _ _).mp he),?_,?_⟩
  · intro he
    exact noadd _ _ (((fullClass_eq_iff _ _).mp he).trans (EqE.equation .zero_zero).symm)
  · intro he
    exact noadd _ _ (((fullClass_eq_iff _ _).mp he).trans (EqE.equation .zero_one).symm)

/-- Equal semantic values with source-minimum nonnumeric leaves have equal
summary costs, using the actual numeric table for all result handles. -/
theorem expanded_minimum_add_numeric_cost_eq (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (numbers : Fin (n+1) → Nat)
    (hn : ∀ j, EqE (tallyResult ns swap left right rs j) (addNumeral (numbers j)))
    (restricted : Finset Nat) (r s : Recipe (ExpandedHandles n))
    (hr : ∀ a ∈ (r.addNumericSummary (expandedNumericHandles numbers)).atoms,
      MinimalRecipe restricted (expandedFrame ns swap left right rs).value a)
    (hs : ∀ a ∈ (s.addNumericSummary (expandedNumericHandles numbers)).atoms,
      MinimalRecipe restricted (expandedFrame ns swap left right rs).value a)
    (he : EqE ((expandedFrame ns swap left right rs).eval r) ((expandedFrame ns swap left right rs).eval s)) :
    (r.addNumericSummary (expandedNumericHandles numbers)).numericHandleRecipeCost (expandedNumericHandles numbers) =
    (s.addNumericSummary (expandedNumericHandles numbers)).numericHandleRecipeCost (expandedNumericHandles numbers) := by
  let ν := expandedNumericHandles numbers
  have hnumeric : ExpandedResultsNumeric ns swap left right rs := fun j => ⟨numbers j,hn j⟩
  have hrf := Term.addNumericValue_summary (expandedFrame ns swap left right rs).value ν r
    (expanded_minimum_add_numeric_atoms_atomic ns swap left right rs hnumeric numbers restricted r hr)
  have hsf := Term.addNumericValue_summary (expandedFrame ns swap left right rs).value ν s
    (expanded_minimum_add_numeric_atoms_atomic ns swap left right rs hnumeric numbers restricted s hs)
  have her := r.addNumericValue_eq (expandedFrame ns swap left right rs).value ν
    (expanded_numeric_handle_value ns swap left right rs numbers hn)
  have hes := s.addNumericValue_eq (expandedFrame ns swap left right rs).value ν
    (expanded_numeric_handle_value ns swap left right rs numbers hn)
  have hsum := (eqE_iff_add_value_summary _ _ hrf.2 hsf.2).mp (her.symm.trans (he.trans hes))
  rw [hrf.1,hsf.1] at hsum
  have hbag := congrArg AddSummary.atoms hsum
  have hnum := congrArg AddSummary.numeric hsum
  have hcost := minimum_leaf_cost_bags_eq (r.addNumericSummary ν).atoms (s.addNumericSummary ν).atoms hr hs hbag
  have hplus := congrArg (fun xs : Multiset Nat => (xs.map (fun k => k+1)).sum) hcost
  simp only [Multiset.map_map,Function.comp_def] at hplus
  exact congrArg₂ Nat.add hplus (congrArg (numericHandleCost ν) hnum)

/-- Exact numeric-aware summary cost implies global minimum size against every
public recipe, not just against pure addition expressions. -/
theorem expanded_minimum_add_of_exact_numeric_cost (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (numbers : Fin (n+1) → Nat)
    (hn : ∀ j, EqE (tallyResult ns swap left right rs j) (addNumeral (numbers j)))
    (restricted : Finset Nat) (r : Recipe (ExpandedHandles n)) (hp : r.Public restricted)
    (hmin : ∀ a ∈ (r.addNumericSummary (expandedNumericHandles numbers)).atoms,
      MinimalRecipe restricted (expandedFrame ns swap left right rs).value a)
    (hcost : r.nodeCount+1 =
      (r.addNumericSummary (expandedNumericHandles numbers)).numericHandleRecipeCost (expandedNumericHandles numbers)) :
    MinimalRecipe restricted (expandedFrame ns swap left right rs).value r := by
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (expandedFrame ns swap left right rs).value) r hp
  have hc := expanded_minimum_add_numeric_cost_eq ns swap left right rs numbers hn restricted r m hmin
    (fun _ ha => hm.add_numeric_atom _ ha) he
  have hb := m.addNumericSummary_cost_le (expandedNumericHandles numbers)
  exact hm.of_equivalent_size hp he (by omega)

/-- With minimum nonnumeric leaves, an outer addition skeleton has a globally
minimum representative preserving its exact numeric-aware syntax summary. -/
theorem expanded_minimum_add_numeric_representative (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (numbers : Fin (n+1) → Nat)
    (hn : ∀ j, EqE (tallyResult ns swap left right rs j) (addNumeral (numbers j)))
    (restricted : Finset Nat) (r : Recipe (ExpandedHandles n)) (hp : r.Public restricted)
    (hmin : ∀ a ∈ (r.addNumericSummary (expandedNumericHandles numbers)).atoms,
      MinimalRecipe restricted (expandedFrame ns swap left right rs).value a) :
    ∃ s, MinimalRecipe restricted (expandedFrame ns swap left right rs).value s ∧
      s.addNumericSummary (expandedNumericHandles numbers) = r.addNumericSummary (expandedNumericHandles numbers) := by
  obtain ⟨s,hps,hs,hc⟩ := public_numeric_handle_cost_representative (expandedNumericHandles numbers) r hp
  refine ⟨s,expanded_minimum_add_of_exact_numeric_cost ns swap left right rs numbers hn restricted s hps ?_ ?_,hs⟩
  · simpa only [hs] using hmin
  · simpa only [hs] using hc

/-- Addition with minimum children has a shared source-minimum representative
in actual accepted expanded frames. Shared tally numbers discharge all
numeric-table premises; no smaller-observation assumption remains here. -/
theorem accepted_expanded_minimum_children_add_shared (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (a b : Recipe (ExpandedHandles n))
    (hminA : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value a)
    (hminB : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value b) :
    Frame.SharedMinimum (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs) (.binary .add a b) := by
  choose numbers _ hnum using fun j => accepted_sequence_tally_numeric ns hf left right rs hp ha j
  let ν := expandedNumericHandles numbers
  obtain ⟨s,hs,hsum⟩ := expanded_minimum_add_numeric_representative ns swap left right rs numbers
    (fun j => hnum j swap) ns.restricted (.binary .add a b) ⟨hminA.isPublic,hminB.isPublic⟩ (by
      intro x hx
      rcases Multiset.mem_add.mp hx with hxa | hxb
      · exact hminA.add_numeric_atom ν hxa
      · exact hminB.add_numeric_atom ν hxb)
  refine ⟨s,hs,?_,?_⟩
  · exact eqE_of_addNumericSummary_eq _ ν
      (expanded_numeric_handle_value ns swap left right rs numbers (fun j => hnum j swap)) hsum.symm
  · exact eqE_of_addNumericSummary_eq _ ν
      (expanded_numeric_handle_value ns swap' left right rs numbers (fun j => hnum j swap')) hsum.symm

end ExplainableCrypto.Helios.Symbolic.Historical.General
