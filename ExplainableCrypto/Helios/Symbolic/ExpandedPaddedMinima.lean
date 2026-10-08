import ExplainableCrypto.Helios.Symbolic.PaddedNumericHandleCosts
import ExplainableCrypto.Helios.Symbolic.ExpandedAddMinimumClosure

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Padded semantic equality fixes the minimum atom-cost bag and total. The
numeric table prices all positive totals, including cheap published numerals. -/
theorem expanded_minimum_padded_numeric_cost_eq (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (numbers : Fin (n+1) → Nat) (hn : ∀ j, EqE (tallyResult ns swap left right rs j) (addNumeral (numbers j)))
    (restricted : Finset Nat) (r s : Recipe (ExpandedHandles n))
    (hr : ∀ a ∈ (r.addNumericSummary (expandedNumericHandles numbers)).atoms,
      MinimalRecipe restricted (expandedFrame ns swap left right rs).value a)
    (hs : ∀ a ∈ (s.addNumericSummary (expandedNumericHandles numbers)).atoms,
      MinimalRecipe restricted (expandedFrame ns swap left right rs).value a)
    (he : EqE ((expandedFrame ns swap left right rs).eval (.binary .add r (.const .zero)))
      ((expandedFrame ns swap left right rs).eval (.binary .add s (.const .zero)))) :
    (r.addNumericSummary (expandedNumericHandles numbers)).paddedNumericHandleRecipeCost (expandedNumericHandles numbers) =
    (s.addNumericSummary (expandedNumericHandles numbers)).paddedNumericHandleRecipeCost (expandedNumericHandles numbers) := by
  let ν := expandedNumericHandles numbers
  have hnumeric : ExpandedResultsNumeric ns swap left right rs := fun j => ⟨numbers j,hn j⟩
  have hrp : ∀ a ∈ (Term.binary .add r (.const .zero)).addNumericSummary ν |>.atoms,
      MinimalRecipe restricted (expandedFrame ns swap left right rs).value a := by
    simpa only [Term.padded_addNumericSummary] using hr
  have hsp : ∀ a ∈ (Term.binary .add s (.const .zero)).addNumericSummary ν |>.atoms,
      MinimalRecipe restricted (expandedFrame ns swap left right rs).value a := by
    simpa only [Term.padded_addNumericSummary] using hs
  have hrf := Term.addNumericValue_summary (expandedFrame ns swap left right rs).value ν (.binary .add r (.const .zero))
    (expanded_minimum_add_numeric_atoms_atomic ns swap left right rs hnumeric numbers restricted _ hrp)
  have hsf := Term.addNumericValue_summary (expandedFrame ns swap left right rs).value ν (.binary .add s (.const .zero))
    (expanded_minimum_add_numeric_atoms_atomic ns swap left right rs hnumeric numbers restricted _ hsp)
  have her := (Term.binary .add r (.const .zero)).addNumericValue_eq (expandedFrame ns swap left right rs).value ν
    (expanded_numeric_handle_value ns swap left right rs numbers hn)
  have hes := (Term.binary .add s (.const .zero)).addNumericValue_eq (expandedFrame ns swap left right rs).value ν
    (expanded_numeric_handle_value ns swap left right rs numbers hn)
  have hsum := (eqE_iff_add_value_summary _ _ hrf.2 hsf.2).mp (her.symm.trans (he.trans hes))
  rw [hrf.1,hsf.1,Term.padded_addNumericSummary,Term.padded_addNumericSummary] at hsum
  have hbag := congrArg AddSummary.atoms hsum
  have hnum := Option.some.inj (congrArg AddSummary.numeric hsum)
  have hcost := minimum_leaf_cost_bags_eq (r.addNumericSummary ν).atoms (s.addNumericSummary ν).atoms hr hs hbag
  have hplus := congrArg (fun xs : Multiset Nat => (xs.map (fun k => k+1)).sum) hcost
  simp only [Multiset.map_map,Function.comp_def] at hplus
  simp only [AddSummary.paddedNumericHandleRecipeCost]
  rw [hplus,hnum]

/-- Attaining padded numeric-handle cost establishes global padded minimum
size against every public recipe, not only addition-shaped competitors. -/
theorem expanded_padded_minimum_of_exact_numeric_cost (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (numbers : Fin (n+1) → Nat) (hn : ∀ j, EqE (tallyResult ns swap left right rs j) (addNumeral (numbers j)))
    (restricted : Finset Nat) (r : Recipe (ExpandedHandles n)) (hp : r.Public restricted)
    (hmin : ∀ a ∈ (r.addNumericSummary (expandedNumericHandles numbers)).atoms,
      MinimalRecipe restricted (expandedFrame ns swap left right rs).value a)
    (hcost : r.nodeCount+1=(r.addNumericSummary (expandedNumericHandles numbers)).paddedNumericHandleRecipeCost (expandedNumericHandles numbers)) :
    PaddedMinimalRecipe restricted (expandedFrame ns swap left right rs).value r := by
  refine ⟨hp,?_⟩
  intro q hq he
  obtain ⟨m,hm,hqm⟩ := exists_minimal_recipe (σ := (expandedFrame ns swap left right rs).value) q hq
  have hle := hm.least q hq hqm.symm
  have hpad := he.trans (.binary .add hqm (.refl _))
  have hc := expanded_minimum_padded_numeric_cost_eq ns swap left right rs numbers hn restricted r m hmin
    (fun a ha => hm.add_numeric_atom _ ha) hpad
  have hb := m.paddedNumericHandleRecipeCost_le (expandedNumericHandles numbers)
  omega

/-- A minimum-atom skeleton has a global padded minimum with the same exact
atom bag and numeric total. Those data preserve padded values in every world
satisfying the same table; the representative is no larger than the source. -/
theorem expanded_padded_minimum_representative (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (numbers : Fin (n+1) → Nat) (hn : ∀ j, EqE (tallyResult ns swap left right rs j) (addNumeral (numbers j)))
    (restricted : Finset Nat) (r : Recipe (ExpandedHandles n)) (hp : r.Public restricted)
    (hmin : ∀ a ∈ (r.addNumericSummary (expandedNumericHandles numbers)).atoms,
      MinimalRecipe restricted (expandedFrame ns swap left right rs).value a) :
    ∃ s, PaddedMinimalRecipe restricted (expandedFrame ns swap left right rs).value s ∧
      (s.addNumericSummary (expandedNumericHandles numbers)).atoms=(r.addNumericSummary (expandedNumericHandles numbers)).atoms ∧
      (s.addNumericSummary (expandedNumericHandles numbers)).numeric.getD 0=(r.addNumericSummary (expandedNumericHandles numbers)).numeric.getD 0 ∧
      s.nodeCount≤r.nodeCount := by
  obtain ⟨s,hps,ha,ht,hc⟩ := public_padded_numeric_handle_cost_representative (expandedNumericHandles numbers) r hp
  have hs : ∀ a ∈ (s.addNumericSummary (expandedNumericHandles numbers)).atoms,
      MinimalRecipe restricted (expandedFrame ns swap left right rs).value a := by simpa only [ha] using hmin
  have he := padded_eqE_of_addNumericSummary (expandedFrame ns swap left right rs).value (expandedNumericHandles numbers)
    (expanded_numeric_handle_value ns swap left right rs numbers hn) ha ht
  have heq := expanded_minimum_padded_numeric_cost_eq ns swap left right rs numbers hn restricted s r hs hmin he
  have hbound := r.paddedNumericHandleRecipeCost_le (expandedNumericHandles numbers)
  exact ⟨s,expanded_padded_minimum_of_exact_numeric_cost ns swap left right rs numbers hn restricted s hps hs (by omega),ha,ht,by omega⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General
