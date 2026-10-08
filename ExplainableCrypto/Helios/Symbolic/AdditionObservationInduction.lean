import ExplainableCrypto.Helios.Symbolic.AdditionLeaves
import ExplainableCrypto.Helios.Symbolic.CompositionObservationInduction

namespace ExplainableCrypto.Helios.Symbolic
variable {restricted : Finset Nat} {handles : Nat}

/-- For addition/bit recipes, all nonnumeric leaves are strictly smaller. Their
pairwise equality tests transfer the atom multiset; literal numeric counts stay fixed. -/
theorem addition_leaf_summary_transfer (φ ψ : Frame restricted handles) (r s : Recipe handles)
    (hp : r.Public restricted) (hq : s.Public restricted)
    (hr : (∃ a b, r = .binary .add a b) ∨ r = .const .zero ∨ r = .const .one)
    (hs : (∃ a b, s = .binary .add a b) ∨ s = .const .zero ∨ s = .const .one)
    (hobs : φ.ObservationsBelow ψ (r.nodeCount + s.nodeCount)) :
    (AddSummary.mk (r.addSyntaxSummary.atoms.map (fun a => (φ.eval a).fullClass)) r.addSyntaxSummary.numeric =
      AddSummary.mk (s.addSyntaxSummary.atoms.map (fun a => (φ.eval a).fullClass)) s.addSyntaxSummary.numeric) ↔
    (AddSummary.mk (r.addSyntaxSummary.atoms.map (fun a => (ψ.eval a).fullClass)) r.addSyntaxSummary.numeric =
      AddSummary.mk (s.addSyntaxSummary.atoms.map (fun a => (ψ.eval a).fullClass)) s.addSyntaxSummary.numeric) := by
  simp only [AddSummary.mk.injEq]
  apply and_congr_left
  intro _
  apply multiset_mapped_equality_transfer
  intro x hx y hy
  obtain ⟨⟨cx, hcx⟩, _⟩ := Term.addSyntaxSummary_mem hx
  obtain ⟨⟨cy, hcy⟩, _⟩ := Term.addSyntaxSummary_mem hy
  have hpx : x.Public restricted := cx.public_hole (by simpa only [hcx] using hp)
  have hpy : y.Public restricted := cy.public_hole (by simpa only [hcy] using hq)
  have hsx := Term.add_leaf_smaller hr hx
  have hsy := Term.add_leaf_smaller hs hy
  exact (fullClass_eq_iff _ _).trans ((hobs x y hpx hpy (by omega)).trans (fullClass_eq_iff _ _).symm)

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- The complete addition-valued minimum branch includes numeric collapses.
Both semantic atom conditions and literal numeric accounting are derived;
equality transfers from strictly smaller public observations in both directions. -/
theorem minimum_addition_equality_swap (ns : Names n)
    (left right : CandidateSubstitution n Empty) (r s : Recipe 3)
    (hr : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hs : MinimalRecipe ns.restricted (frame ns false left right).value s)
    {x y u v : Ground}
    (her : EqE ((frame ns false left right).eval r) (.binary .add x y))
    (hes : EqE ((frame ns false left right).eval s) (.binary .add u v))
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      (r.nodeCount + s.nodeCount)) :
    EqE ((frame ns false left right).eval r) ((frame ns false left right).eval s) ↔
      EqE ((frame ns true left right).eval r) ((frame ns true left right).eval s) := by
  have har := minimum_add_leaf_values ns left right r hr (hobs.mono (by omega))
  have has := minimum_add_leaf_values ns left right s hs (hobs.mono (by omega))
  have hrf := Term.add_leaves_substitution (frame ns false left right).value r har.1
  have hsf := Term.add_leaves_substitution (frame ns false left right).value s has.1
  have hrt := Term.add_leaves_substitution (frame ns true left right).value r har.2
  have hst := Term.add_leaves_substitution (frame ns true left right).value s has.2
  have hf := eqE_iff_add_value_summary _ _ hrf.2 hsf.2
  have ht := eqE_iff_add_value_summary _ _ hrt.2 hst.2
  rw [hrf.1, hsf.1] at hf
  rw [hrt.1, hst.1] at ht
  have hrform := minimum_add_form ns false left right ns.restricted r hr her
  have hsform := minimum_add_form ns false left right ns.restricted s hs hes
  exact hf.trans ((addition_leaf_summary_transfer _ _ r s hr.isPublic hs.isPublic hrform hsform hobs).trans ht.symm)

end ExplainableCrypto.Helios.Symbolic.Historical.General
