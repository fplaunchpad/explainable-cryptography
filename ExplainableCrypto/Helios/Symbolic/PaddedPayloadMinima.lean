import ExplainableCrypto.Helios.Symbolic.PaddedPayloadCosts

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type} {restricted : Finset Nat} {σ : V → Term W}

/-- Least public recipe size in a zero-padded equality class. This changes
the minimization relation, not the symbolic equations or public-name policy. -/
def PaddedMinimalRecipe (restricted : Finset Nat) (σ : V → Term W) (r : Term V) : Prop :=
  r.Public restricted ∧ ∀ s, s.Public restricted →
    EqE ((Term.binary .add r (.const .zero)).subst σ)
      ((Term.binary .add s (.const .zero)).subst σ) → r.nodeCount ≤ s.nodeCount

theorem PaddedMinimalRecipe.minimum {r : Term V} (h : PaddedMinimalRecipe restricted σ r) :
    MinimalRecipe restricted σ r :=
  ⟨h.1,fun s hp he => h.2 s hp (.binary .add he (.refl _))⟩

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Padded equalities fix the minimum-atom cost bag and the number of ones.
Numeric absence and a present zero both contribute zero to that latter count. -/
theorem minimum_padded_summary_cost_eq (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r s : Recipe 3)
    (hr : ∀ a ∈ r.addSyntaxSummary.atoms, MinimalRecipe restricted (frame ns swap left right).value a)
    (hs : ∀ a ∈ s.addSyntaxSummary.atoms, MinimalRecipe restricted (frame ns swap left right).value a)
    (he : EqE ((frame ns swap left right).eval (.binary .add r (.const .zero)))
      ((frame ns swap left right).eval (.binary .add s (.const .zero)))) :
    r.addSyntaxSummary.paddedRecipeCost=s.addSyntaxSummary.paddedRecipeCost := by
  have hrp : ∀ a ∈ (Term.binary .add r (.const .zero)).addSyntaxSummary.atoms,
      MinimalRecipe restricted (frame ns swap left right).value a := by
    simpa only [Term.padded_addSyntaxSummary] using hr
  have hsp : ∀ a ∈ (Term.binary .add s (.const .zero)).addSyntaxSummary.atoms,
      MinimalRecipe restricted (frame ns swap left right).value a := by
    simpa only [Term.padded_addSyntaxSummary] using hs
  have hrf := Term.add_leaves_substitution (frame ns swap left right).value (.binary .add r (.const .zero))
    (minimum_add_atoms_atomic ns swap left right restricted _ hrp)
  have hsf := Term.add_leaves_substitution (frame ns swap left right).value (.binary .add s (.const .zero))
    (minimum_add_atoms_atomic ns swap left right restricted _ hsp)
  have hsum := (eqE_iff_add_value_summary _ _ hrf.2 hsf.2).mp he
  rw [hrf.1,hsf.1,Term.padded_addSyntaxSummary,Term.padded_addSyntaxSummary] at hsum
  have hbag := congrArg AddSummary.atoms hsum
  have hnum := Option.some.inj (congrArg AddSummary.numeric hsum)
  have hcost := minimum_leaf_cost_bags_eq r.addSyntaxSummary.atoms s.addSyntaxSummary.atoms hr hs hbag
  have hplus := congrArg (fun xs : Multiset Nat => (xs.map (fun k => k+1)).sum) hcost
  simp only [Multiset.map_map,Function.comp_def] at hplus
  simp only [AddSummary.paddedRecipeCost]
  rw [hplus,hnum]

/-- Attaining the padded cost gives global minimality against all public
padded-equal competitors, not just recipes already in an addition normal form. -/
theorem padded_minimum_of_exact_cost (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hp : r.Public restricted)
    (hmin : ∀ a ∈ r.addSyntaxSummary.atoms, MinimalRecipe restricted (frame ns swap left right).value a)
    (hcost : r.nodeCount+1=r.addSyntaxSummary.paddedRecipeCost) :
    PaddedMinimalRecipe restricted (frame ns swap left right).value r := by
  refine ⟨hp,?_⟩
  intro q hq he
  obtain ⟨m,hm,hqm⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value) q hq
  have hle := hm.least q hq hqm.symm
  have hpad := he.trans (.binary .add hqm (.refl _))
  have hc := minimum_padded_summary_cost_eq ns swap left right restricted r m hmin
    (fun a ha => hm.add_atom ha) hpad
  have hb := m.paddedRecipeCost_le
  omega

/-- An outer skeleton with minimum atoms has a global padded minimum, shared
under every substitution after padding via raw E0 equality. -/
theorem padded_minimum_representative (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hp : r.Public restricted)
    (hmin : ∀ a ∈ r.addSyntaxSummary.atoms, MinimalRecipe restricted (frame ns swap left right).value a) :
    ∃ s, PaddedMinimalRecipe restricted (frame ns swap left right).value s ∧
      BaseEq (.binary .add r (.const .zero)) (.binary .add s (.const .zero)) ∧ s.nodeCount≤r.nodeCount := by
  obtain ⟨s,hps,he,ha,hc⟩ := public_padded_minimum_cost_representative r hp
  have hm := padded_minimum_of_exact_cost ns swap left right restricted s hps
    (by simpa only [ha] using hmin)
  have heq := minimum_padded_summary_cost_eq ns swap left right restricted r s hmin
    (by simpa only [ha] using hmin) (he.sound.subst _)
  have hb := r.paddedRecipeCost_le
  exact ⟨s,hm (by omega),he,by omega⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General
