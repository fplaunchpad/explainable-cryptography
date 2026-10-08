import ExplainableCrypto.Helios.Symbolic.CompositionLeaves

namespace ExplainableCrypto.Helios.Symbolic
variable {restricted : Finset Nat} {handles : Nat}

/-- Equality of two bags depends only on equality comparisons between their
members, while preserving multiplicity rather than merely set membership. -/
theorem multiset_mapped_equality_transfer {A B C : Type} (xs ys : Multiset A) (f : A → B) (g : A → C)
    (h : ∀ x ∈ xs, ∀ y ∈ ys, f x = f y ↔ g x = g y) :
    xs.map f = ys.map f ↔ xs.map g = ys.map g := by
  rw [← Multiset.rel_eq, Multiset.rel_map, ← Multiset.rel_eq, Multiset.rel_map]
  constructor
  · intro he
    exact he.mono (fun x hx y hy hxy => (h x hx y hy).mp hxy)
  · intro he
    exact he.mono (fun x hx y hy hxy => (h x hx y hy).mpr hxy)

/-- Raw composition leaves are public and strictly smaller than their trees.
Thus the original comparison bound transfers their full-E class bag equality. -/
theorem composition_leaf_bag_transfer (φ ψ : Frame restricted handles) (a b c d : Recipe handles)
    (hp : (Term.binary .compose a b).Public restricted) (hq : (Term.binary .compose c d).Public restricted)
    (hobs : φ.ObservationsBelow ψ
      ((Term.binary .compose a b).nodeCount + (Term.binary .compose c d).nodeCount)) :
    (Term.binary .compose a b).composeLeaves.map (fun r => (φ.eval r).fullClass) =
      (Term.binary .compose c d).composeLeaves.map (fun r => (φ.eval r).fullClass) ↔
    (Term.binary .compose a b).composeLeaves.map (fun r => (ψ.eval r).fullClass) =
      (Term.binary .compose c d).composeLeaves.map (fun r => (ψ.eval r).fullClass) := by
  apply multiset_mapped_equality_transfer
  intro x hx y hy
  obtain ⟨⟨cx, hcx⟩, _⟩ := Term.composeLeaves_mem hx
  obtain ⟨⟨cy, hcy⟩, _⟩ := Term.composeLeaves_mem hy
  have hpx : x.Public restricted := cx.public_hole (by simpa only [hcx] using hp)
  have hpy : y.Public restricted := cy.public_hole (by simpa only [hcy] using hq)
  have hsx := Term.compose_leaf_smaller a b x hx
  have hsy := Term.compose_leaf_smaller c d y hy
  exact (fullClass_eq_iff _ _).trans ((hobs x y hpx hpy (by omega)).trans (fullClass_eq_iff _ _).symm)

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- The complete composition-valued minimum branch derives raw syntax and
semantic atom conditions in both worlds, then compares strictly smaller leaves.
No destination minimum-size or fixed factor-value premise is assumed. -/
theorem minimum_composition_equality_swap (ns : Names n)
    (left right : CandidateSubstitution n Empty) (r s : Recipe 3)
    (hr : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hs : MinimalRecipe ns.restricted (frame ns false left right).value s)
    {x y u v : Ground}
    (her : EqE ((frame ns false left right).eval r) (.binary .compose x y))
    (hes : EqE ((frame ns false left right).eval s) (.binary .compose u v))
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      (r.nodeCount + s.nodeCount)) :
    EqE ((frame ns false left right).eval r) ((frame ns false left right).eval s) ↔
      EqE ((frame ns true left right).eval r) ((frame ns true left right).eval s) := by
  have har := minimum_compose_leaf_values ns left right r hr (hobs.mono (by omega))
  have has := minimum_compose_leaf_values ns left right s hs (hobs.mono (by omega))
  have hrf := Term.compose_leaves_substitution (frame ns false left right).value r har.1
  have hsf := Term.compose_leaves_substitution (frame ns false left right).value s has.1
  have hrt := Term.compose_leaves_substitution (frame ns true left right).value r har.2
  have hst := Term.compose_leaves_substitution (frame ns true left right).value s has.2
  have hf := eqE_iff_compose_value_factors _ _ hrf.2 hsf.2
  have ht := eqE_iff_compose_value_factors _ _ hrt.2 hst.2
  rw [hrf.1, hsf.1] at hf
  rw [hrt.1, hst.1] at ht
  obtain ⟨a, b, rfl⟩ := minimum_compose_form ns false left right ns.restricted r hr her
  obtain ⟨c, d, rfl⟩ := minimum_compose_form ns false left right ns.restricted s hs hes
  exact hf.trans ((composition_leaf_bag_transfer _ _ a b c d hr.isPublic hs.isPublic hobs).trans ht.symm)

end ExplainableCrypto.Helios.Symbolic.Historical.General
