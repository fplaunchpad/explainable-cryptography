import ExplainableCrypto.Helios.Symbolic.AdditionMinimumRealization

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Minimum nonnumeric raw leaves remain semantic addition atoms in the
initial frame, under any caller policy. -/
theorem minimum_add_atoms_atomic (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hmin : ∀ a ∈ r.addSyntaxSummary.atoms,
      MinimalRecipe restricted (frame ns swap left right).value a) :
    ∀ a ∈ r.addSyntaxSummary.atoms, ((frame ns swap left right).eval a).fullClass.AddAtom := by
  intro a ha
  obtain ⟨_,hn,hz,ho⟩ := Term.addSyntaxSummary_mem ha
  have noadd : ∀ x y, ¬ EqE ((frame ns swap left right).eval a) (.binary .add x y) := by
    intro x y he
    rcases minimum_add_form ns swap left right restricted a (hmin a ha) he with ⟨u,v,h⟩ | h | h
    · exact hn u v h
    · exact hz h
    · exact ho h
  refine ⟨fun x y he => noadd x y ((fullClass_eq_iff _ _).mp he),?_,?_⟩
  · intro he
    exact noadd _ _ (((fullClass_eq_iff _ _).mp he).trans (EqE.equation .zero_zero).symm)
  · intro he
    exact noadd _ _ (((fullClass_eq_iff _ _).mp he).trans (EqE.equation .zero_one).symm)

/-- Equal evaluated addition summaries have equal raw minimum-leaf costs.
Optional numeric presence and multiplicity are preserved explicitly. -/
theorem minimum_add_summary_cost_eq (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r s : Recipe 3)
    (hr : ∀ a ∈ r.addSyntaxSummary.atoms, MinimalRecipe restricted (frame ns swap left right).value a)
    (hs : ∀ a ∈ s.addSyntaxSummary.atoms, MinimalRecipe restricted (frame ns swap left right).value a)
    (he : EqE ((frame ns swap left right).eval r) ((frame ns swap left right).eval s)) :
    r.addSyntaxSummary.recipeCost = s.addSyntaxSummary.recipeCost := by
  have hrf := Term.add_leaves_substitution (frame ns swap left right).value r
    (minimum_add_atoms_atomic ns swap left right restricted r hr)
  have hsf := Term.add_leaves_substitution (frame ns swap left right).value s
    (minimum_add_atoms_atomic ns swap left right restricted s hs)
  have hsum := (eqE_iff_add_value_summary _ _ hrf.2 hsf.2).mp he
  rw [hrf.1,hsf.1] at hsum
  have hbag := congrArg AddSummary.atoms hsum
  have hnum := congrArg AddSummary.numeric hsum
  have hcost := minimum_leaf_cost_bags_eq r.addSyntaxSummary.atoms s.addSyntaxSummary.atoms hr hs hbag
  have hplus := congrArg (fun xs : Multiset Nat => (xs.map (fun k => k+1)).sum) hcost
  simp only [Multiset.map_map,Function.comp_def] at hplus
  exact congrArg₂ Nat.add hplus (congrArg numericRecipeCost hnum)

/-- Attaining the raw summary cost implies global source minimality when the
nonnumeric leaves are minimum. Compare against an arbitrary minimum equivalent. -/
theorem minimum_add_of_exact_cost (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hp : r.Public restricted)
    (hmin : ∀ a ∈ r.addSyntaxSummary.atoms, MinimalRecipe restricted (frame ns swap left right).value a)
    (hcost : r.nodeCount+1 = r.addSyntaxSummary.recipeCost) :
    MinimalRecipe restricted (frame ns swap left right).value r := by
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value) r hp
  have hc := minimum_add_summary_cost_eq ns swap left right restricted r m hmin
    (fun _ ha => hm.add_atom ha) he
  have hb := m.addSyntaxSummary_cost_le
  exact hm.of_equivalent_size hp he (by omega)

/-- An outer addition skeleton with minimum atoms has a globally minimum
representative equal already in raw E0, before any frame substitution. -/
theorem minimum_add_representative (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hp : r.Public restricted)
    (hmin : ∀ a ∈ r.addSyntaxSummary.atoms, MinimalRecipe restricted (frame ns swap left right).value a) :
    ∃ s, MinimalRecipe restricted (frame ns swap left right).value s ∧ BaseEq r s := by
  obtain ⟨s,hp,he,hs,hc⟩ := public_addition_minimum_cost_representative r hp
  refine ⟨s,minimum_add_of_exact_cost ns swap left right restricted s hp ?_ ?_,he⟩
  · simpa only [hs] using hmin
  · simpa only [hs] using hc

/-- Addition with minimum children has a shared source-minimum representative
in every destination frame using the same public-name policy. -/
theorem minimum_children_add_shared (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (a b : Recipe 3)
    (ha : MinimalRecipe ns.restricted (frame ns swap left right).value a)
    (hb : MinimalRecipe ns.restricted (frame ns swap left right).value b)
    (ψ : Frame ns.restricted 3) :
    Frame.SharedMinimum (frame ns swap left right) ψ (.binary .add a b) := by
  obtain ⟨s,hs,he⟩ := minimum_add_representative ns swap left right ns.restricted
    (.binary .add a b) ⟨ha.isPublic,hb.isPublic⟩ (by
      intro x hx
      rcases Multiset.mem_add.mp hx with hxa | hxb
      · exact ha.add_atom hxa
      · exact hb.add_atom hxb)
  exact .of_recipe_eqE hs he.sound

end ExplainableCrypto.Helios.Symbolic.Historical.General
