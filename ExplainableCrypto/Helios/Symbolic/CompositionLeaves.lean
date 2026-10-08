import ExplainableCrypto.Helios.Symbolic.MinimumCompositionOrigins

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type}

/-- Raw outer-composition leaves, preserving duplicate occurrences. -/
def Term.composeLeaves : Term V → Multiset (Term V)
  | .binary .compose a b => a.composeLeaves + b.composeLeaves
  | t => {t}

/-- Every flattened leaf is a genuine syntactic subterm and is not a raw
composition node. Its value may still be reducible. -/
theorem Term.composeLeaves_mem {r a : Term V} (ha : a ∈ r.composeLeaves) :
    (∃ c : Context V, c.fill a = r) ∧ (∀ x y, a ≠ .binary .compose x y) := by
  induction r with
  | binary f x y ix iy =>
    cases f with
    | compose =>
      rcases Multiset.mem_add.mp ha with hx | hy
      · obtain ⟨⟨c, hc⟩, hn⟩ := ix hx
        exact ⟨⟨.binaryLeft .compose c y, by simp only [Context.fill, hc]⟩, hn⟩
      · obtain ⟨⟨c, hc⟩, hn⟩ := iy hy
        exact ⟨⟨.binaryRight .compose x c, by simp only [Context.fill, hc]⟩, hn⟩
    | pair | mul | add | partialDecrypt | dec =>
      have he : a = _ := Multiset.mem_singleton.mp ha
      subst a
      exact ⟨⟨.hole, rfl⟩, by intro _ _ h; cases h⟩
  | name | var | const | unary | ternary | spk =>
    have he : a = _ := Multiset.mem_singleton.mp ha
    subst a
    exact ⟨⟨.hole, rfl⟩, by intro _ _ h; cases h⟩

/-- Filling a context never makes its hole smaller in raw node count. -/
theorem Context.nodeCount_hole_le (c : Context V) (a : Term V) : a.nodeCount ≤ (c.fill a).nodeCount := by
  have hb := c.nodeCount_balance a (.const .bottom)
  have hp := (c.fill (.const .bottom)).nodeCount_pos
  simp only [Term.nodeCount] at hb
  omega

/-- Every leaf of a nontrivial composition is strictly smaller than the tree. -/
theorem Term.compose_leaf_smaller (a b leaf : Term V)
    (h : leaf ∈ (Term.binary .compose a b).composeLeaves) :
    leaf.nodeCount < (Term.binary .compose a b).nodeCount := by
  rcases Multiset.mem_add.mp h with ha | hb
  · obtain ⟨⟨c, hc⟩, _⟩ := Term.composeLeaves_mem ha
    have hle := c.nodeCount_hole_le leaf
    rw [hc] at hle
    simp only [Term.nodeCount]
    omega
  · obtain ⟨⟨c, hc⟩, _⟩ := Term.composeLeaves_mem hb
    have hle := c.nodeCount_hole_le leaf
    rw [hc] at hle
    simp only [Term.nodeCount]
    omega

private theorem singleton_atomic {t : Term W}
    (h : ∀ x y, ¬ EqE t (.binary .compose x y)) :
    t.composeValueFactors = {t.fullClass} ∧ t.AtomicComposeFactors := by
  have hf := Term.composeValueFactors_singleton (t := t) (by
    intro a b he; subst t; exact h a b (.refl _))
  refine ⟨hf, ?_⟩
  intro q hq x y he
  rw [hf, Multiset.mem_singleton] at hq
  subst q
  exact h x y ((fullClass_eq_iff _ _).mp he)

private theorem singleton_substitution (σ : V → Term W) (r : Term V)
    (hr : r.composeLeaves = {r})
    (h : ∀ a ∈ r.composeLeaves, ∀ x y, ¬ EqE (a.subst σ) (.binary .compose x y)) :
    (r.subst σ).composeValueFactors = r.composeLeaves.map (fun a => (a.subst σ).fullClass) ∧
    (r.subst σ).AtomicComposeFactors := by
  rw [hr, Multiset.map_singleton]
  exact singleton_atomic (h r (by rw [hr]; simp))

/-- Substitution preserves the raw leaf factorization when no evaluated leaf
can itself have a composition E-value. This semantic premise permits reduction. -/
theorem Term.compose_leaves_substitution (σ : V → Term W) (r : Term V)
    (h : ∀ a ∈ r.composeLeaves, ∀ x y, ¬ EqE (a.subst σ) (.binary .compose x y)) :
    (r.subst σ).composeValueFactors = r.composeLeaves.map (fun a => (a.subst σ).fullClass) ∧
    (r.subst σ).AtomicComposeFactors := by
  induction r with
  | binary f a b ia ib =>
    cases f with
    | compose =>
      have ha := ia (fun x hx => h x (Multiset.mem_add.mpr (Or.inl hx)))
      have hb := ib (fun x hx => h x (Multiset.mem_add.mpr (Or.inr hx)))
      refine ⟨?_, ?_⟩
      · simp only [Term.subst, Term.composeValueFactors, Term.composeLeaves, Multiset.map_add, ha.1, hb.1]
      · intro q hq
        rcases Multiset.mem_add.mp hq with hqa | hqb
        · exact ha.2 q hqa
        · exact hb.2 q hqb
    | pair | mul | add | partialDecrypt | dec => exact singleton_substitution σ _ rfl h
  | _ => exact singleton_substitution σ _ rfl h

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Minimum raw leaves are semantic composition atoms in both worlds. Their
no-composition obligations follow from exact origins and smaller observations. -/
theorem minimum_compose_leaf_values (ns : Names n)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right) r.nodeCount) :
    (∀ a ∈ r.composeLeaves, ∀ x y, ¬ EqE ((frame ns false left right).eval a) (.binary .compose x y)) ∧
    (∀ a ∈ r.composeLeaves, ∀ x y, ¬ EqE ((frame ns true left right).eval a) (.binary .compose x y)) := by
  have info {a : Recipe 3} (ha : a ∈ r.composeLeaves) :
      MinimalRecipe ns.restricted (frame ns false left right).value a ∧
      a.nodeCount ≤ r.nodeCount ∧ (∀ x y, a ≠ .binary .compose x y) := by
    obtain ⟨⟨c, hc⟩, hn⟩ := Term.composeLeaves_mem ha
    have hmc := hm
    rw [← hc] at hmc
    exact ⟨hmc.subterm c, by simpa only [hc] using c.nodeCount_hole_le a, hn⟩
  constructor
  · intro a ha x y he
    have hi := info ha
    obtain ⟨u, v, hu⟩ := minimum_compose_form ns false left right ns.restricted a hi.1 he
    exact hi.2.2 u v hu
  · intro a ha x y he
    have hi := info ha
    obtain ⟨u, v, hu⟩ := minimum_compose_form_after_swap ns left right a hi.1 (hobs.mono hi.2.1) he
    exact hi.2.2 u v hu

end ExplainableCrypto.Helios.Symbolic.Historical.General
