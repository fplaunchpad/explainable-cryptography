import ExplainableCrypto.Helios.Symbolic.ExpandedPairMinimumTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedPairMinimumExperiments
import ExplainableCrypto.Helios.Symbolic.ExpandedPairSPOT
import ExplainableCrypto.Helios.Symbolic.ExpandedCheckSPOT

namespace ExplainableCrypto.Helios.Symbolic.ExpandedPairMinimumSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []
abbrev tail (i : Fin 2) (k : Nat) : Recipe (ExpandedHandles 1) := (Term.var (expandedOld i.succ)).drop k
private theorem numeric (swap : Bool) : ExpandedResultsNumeric names swap left right [] :=
  accepted_expanded_results_numeric names HistoricalFrameSPOT.fixture_names_fresh left right [] (by simp) trivial swap
private theorem tail_minimum (swap : Bool) (i : Fin 2) (k : Nat) (hk : k<5) :
    MinimalRecipe names.restricted (world swap).value (tail i k) :=
  expanded_minimum_ballot_tail names HistoricalFrameSPOT.fixture_names_fresh swap left right [] (by simp) (numeric swap) i k hk
private theorem public40 : (Term.name (V := Fin (ExpandedHandles 1)) 40).Public names.restricted := by
  change 40 ∉ names.restricted; decide

/-- Every nonempty tail has the independently counted k+1 nodes and is globally
minimum; every minimum equivalent has exactly that raw voter/tail syntax. -/
theorem nonempty_tail_minimum_and_origin (swap : Bool) (i : Fin 2) (k : Nat) (hk : k<5) :
    MinimalRecipe names.restricted (world swap).value (tail i k) ∧ (tail i k).nodeCount=k+1 ∧
    ∀ r, MinimalRecipe names.restricted (world swap).value r → EqE ((world swap).eval r) ((world swap).eval (tail i k)) → r=tail i k :=
  ⟨tail_minimum swap i k hk,by simp [tail,Term.drop_nodeCount,Term.nodeCount,Nat.add_comm],
    fun r hm he => expanded_minimum_honest_tail_origin names HistoricalFrameSPOT.fixture_names_fresh swap left right []
      (by simp) (numeric swap) r hm i k hk he⟩

/-- Two minimum two-node selectors form a five-node pair with a one-node
shared minimum. The general pair theorem handles actual different votes. -/
theorem borrowed_pair_compression (swap swap' : Bool) :
    let a : Recipe (ExpandedHandles 1) := .unary .fst (.var (expandedOld 1))
    let b := tail 0 1
    MinimalRecipe names.restricted (world swap).value a ∧ MinimalRecipe names.restricted (world swap).value b ∧
      ∃ m, MinimalRecipe names.restricted (world swap).value m ∧ m.nodeCount=1 ∧
        EqE ((world swap).eval (.binary .pair a b)) ((world swap).eval m) ∧
        EqE ((world swap').eval (.binary .pair a b)) ((world swap').eval m) ∧
        ¬ MinimalRecipe names.restricted (world swap).value (.binary .pair a b) := by
  have ha := (ExpandedCheckSPOT.first_projection_minimum swap).1
  have hb := tail_minimum swap 0 1 (by decide)
  obtain ⟨m,hm,he,he'⟩ := accepted_expanded_minimum_children_pair_shared names HistoricalFrameSPOT.fixture_names_fresh
    swap swap' left right [] (by simp) trivial _ _ ha hb
  obtain ⟨x,y,hv⟩ := expanded_ballot_tail_pair_value names swap left right [] 0 0 (by decide)
  have hpair : EqE ((world swap).eval (.binary .pair (.unary .fst (.var (expandedOld 1))) (tail 0 1)))
      ((world swap).eval (.var (expandedOld 1))) :=
    (pair_reconstruction_of_value hv).symm
  have hle := hm.least (.var (expandedOld 1)) trivial (he.symm.trans hpair)
  have hpos := m.nodeCount_pos
  refine ⟨ha,hb,m,hm,by change m.nodeCount≤1 at hle; omega,he,he',?_⟩
  intro hh
  exact hh.no_smaller (s := .var (expandedOld 1)) trivial hpair (by decide)

/-- Both projections of a minimum retained ballot handle have shared minima,
with no smaller-test hypotheses. Their minimum output costs are both two. -/
theorem both_honest_selectors_shared (swap swap' : Bool) :
    Frame.SharedMinimum (world swap) (world swap') (.unary .fst (.var (expandedOld 1))) ∧
    Frame.SharedMinimum (world swap) (world swap') (.unary .snd (.var (expandedOld 1))) ∧
    MinimalRecipe names.restricted (world swap).value (.unary .fst (.var (expandedOld 1))) ∧
    MinimalRecipe names.restricted (world swap).value (.unary .snd (.var (expandedOld 1))) :=
  ⟨accepted_expanded_minimum_child_projection_shared names HistoricalFrameSPOT.fixture_names_fresh swap swap' left right []
      (by simp) trivial .fst (Or.inl rfl) _ (.of_nodeCount_one trivial rfl),
    accepted_expanded_minimum_child_projection_shared names HistoricalFrameSPOT.fixture_names_fresh swap swap' left right []
      (by simp) trivial .snd (Or.inr rfl) _ (.of_nodeCount_one trivial rfl),
    (ExpandedCheckSPOT.first_projection_minimum swap).1,tail_minimum swap 0 1 (by decide)⟩

private theorem constructed_pair_minimum (swap : Bool) (v : Fin (ExpandedHandles 1)) :
    MinimalRecipe names.restricted (world swap).value (.binary .pair (.name 40) (.var v)) := by
  have hp : (Term.binary .pair (.name 40) (.var v)).Public names.restricted := ⟨public40,trivial⟩
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (world swap).value) _ hp
  rcases expanded_minimum_pair_observation_form names swap left right [] (numeric swap) names.restricted m hm he.symm with
    ⟨a,b,rfl⟩ | ⟨i,k,hk,rfl⟩
  · have ha := a.nodeCount_pos
    have hb := b.nodeCount_pos
    exact hm.of_equivalent_size hp he (by simp only [Term.nodeCount]; omega)
  · have hfield := ((pair_equality_iff_projections _ _ _ (expanded_ballot_tail_pair_value names swap left right [] i k hk)).mp he).1
    have hbound := expanded_honest_field_public_size_bound names HistoricalFrameSPOT.fixture_names_fresh swap left right []
      (by simp) (numeric swap) (.name 40) public40 i k hk hfield
    have hz : k=0 := by change k+1≤1 at hbound; omega
    subst k
    have hbad := hfield.trans (expanded_honest_selector_value names swap left right [] (i,0))
    obtain ⟨_,_,_,hshape,_⟩ := hbad.symm.penc_irreducible_shape (name_irreducible 40)
    cases hshape

/-- Constructed pairs containing actual published partial/result handles are
minimum, and both fst/snd branches return shared minima in different-vote worlds. -/
theorem constructed_published_pairs (swap swap' : Bool) (v : Fin (ExpandedHandles 1)) :
    let p : Recipe (ExpandedHandles 1) := .binary .pair (.name 40) (.var v)
    MinimalRecipe names.restricted (world swap).value p ∧ p.nodeCount=3 ∧
      Frame.SharedMinimum (world swap) (world swap') (.unary .fst p) ∧
      Frame.SharedMinimum (world swap) (world swap') (.unary .snd p) :=
  ⟨constructed_pair_minimum swap v,rfl,
    accepted_expanded_minimum_child_projection_shared names HistoricalFrameSPOT.fixture_names_fresh swap swap' left right []
      (by simp) trivial .fst (Or.inl rfl) _ (constructed_pair_minimum swap v),
    accepted_expanded_minimum_child_projection_shared names HistoricalFrameSPOT.fixture_names_fresh swap swap' left right []
      (by simp) trivial .snd (Or.inr rfl) _ (constructed_pair_minimum swap v)⟩

/-- The last tail is minimum, but its snd output uses one-node bottom.
Different voters' empty tails coincide, so the nonempty bound is necessary. -/
theorem empty_tail_boundary (swap swap' : Bool) :
    MinimalRecipe names.restricted (world swap).value (tail 0 4) ∧
    Frame.SharedMinimum (world swap) (world swap') (.unary .snd (tail 0 4)) ∧
    EqE ((world swap).eval (tail 0 5)) ((world swap).eval (tail 1 5)) ∧
    ¬ MinimalRecipe names.restricted (world swap).value (.unary .snd (tail 0 4)) :=
  ⟨tail_minimum swap 0 4 (by decide),
    accepted_expanded_minimum_child_projection_shared names HistoricalFrameSPOT.fixture_names_fresh swap swap' left right []
      (by simp) trivial .snd (Or.inr rfl) _ (tail_minimum swap 0 4 (by decide)),
    (expanded_empty_ballot_tail_value names swap left right [] 0).trans (expanded_empty_ballot_tail_value names swap left right [] 1).symm,
    (ExpandedCheckSPOT.empty_tail_projection_not_minimum swap).2⟩

/-- At one candidate, a four-node aggregate selector uses a three-node shared
minimum. The general field origin keeps the component/aggregate alias. -/
theorem one_candidate_aggregate_alias (swap swap' : Bool) :
    let ns := ProofObservationSPOT.oneNames
    let l := ProofObservationSPOT.oneLeft
    let r := ProofObservationSPOT.oneRight
    let φ := expandedFrame ns swap l r []
    let ψ := expandedFrame ns swap' l r []
    let agg : Recipe (ExpandedHandles 0) := (Term.var (expandedOld 1)).project 2
    ∃ m, MinimalRecipe ns.restricted φ.value m ∧ m.nodeCount=3 ∧
      EqE (φ.eval agg) (φ.eval m) ∧ EqE (ψ.eval agg) (ψ.eval m) ∧ agg.nodeCount=4 := by
  let ns := ProofObservationSPOT.oneNames
  let l := ProofObservationSPOT.oneLeft
  let r := ProofObservationSPOT.oneRight
  have hn := accepted_expanded_results_numeric ns NumericReflectionSPOT.fixture_names_fresh l r [] (by simp) trivial swap
  obtain ⟨m,hm,he,he'⟩ := expanded_honest_field_shared_minimum ns NumericReflectionSPOT.fixture_names_fresh swap swap' l r []
    (by simp) hn 0 2 (by decide)
  have halias : EqE ((expandedFrame ns swap l r []).eval ((Term.var (expandedOld 1)).project 2))
      ((expandedFrame ns swap l r []).eval ((Term.var (expandedOld 1)).project 1)) :=
    (expanded_aggregate_proof_value ns swap l r [] 0).trans
      (((component_aggregate_proof_equality_iff ns NumericReflectionSPOT.fixture_names_fresh swap l r 0 0 0).mpr ⟨rfl,rfl⟩).symm.trans
        (expanded_component_proof_value ns swap l r [] 0 0).symm)
  have hle := hm.least ((Term.var (expandedOld 1)).project 1) ((ProjectionChain.project (expandedOld 1) 1).isPublic _)
    (he.symm.trans halias)
  have hge := expanded_honest_field_public_size_bound ns NumericReflectionSPOT.fixture_names_fresh swap l r []
    (by simp) hn m hm.isPublic 0 2 (by decide) he.symm
  exact ⟨m,hm,by change m.nodeCount≤3 at hle; omega,he,he',rfl⟩

/-- A public partial remains a minimum child with a stuck projection. It has
shared selector minima but cannot satisfy pair eta. -/
theorem published_partial_stays_stuck (swap swap' : Bool) :
    Frame.SharedMinimum (world swap) (world swap') (.unary .fst (.var (expandedPartial 0))) ∧
    ¬ EqE ((world swap).eval (.var (expandedPartial 0)))
      ((world swap).eval (.binary .pair (.unary .fst (.var (expandedPartial 0))) (.unary .snd (.var (expandedPartial 0))))) :=
  ⟨accepted_expanded_minimum_child_projection_shared names HistoricalFrameSPOT.fixture_names_fresh swap swap' left right []
      (by simp) trivial .fst (Or.inl rfl) _ (.of_nodeCount_one trivial rfl),ExpandedPairSPOT.partial_pair_eta_is_false swap⟩

/-- Minimum size is necessary for exact tail origins: a reducible wrapper has
the same pair value but lies outside both exact minimum pair forms. -/
theorem minimum_origin_premise_required (swap : Bool) :
    let r : Recipe (ExpandedHandles 1) := .unary .fst (.binary .pair (.var (expandedOld 1)) (.const .bottom))
    EqE ((world swap).eval r) ((world swap).eval (.var (expandedOld 1))) ∧
      ¬ ExpandedPairObservationForm r ∧ ¬ MinimalRecipe names.restricted (world swap).value r :=
  ExpandedPairSPOT.minimum_origin_requires_minimum swap

end ExplainableCrypto.Helios.Symbolic.ExpandedPairMinimumSPOT
