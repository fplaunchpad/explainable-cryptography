import ExplainableCrypto.Helios.Symbolic.ComposeReduction
import ExplainableCrypto.Helios.Symbolic.CiphertextLocalConfluence

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- E0-equivalent source representatives have the same local-confluence property. -/
theorem LocallyConfluentAt.of_base {a b : Term V} (h : LocallyConfluentAt a) (he : BaseEq b a) :
    LocallyConfluentAt b := fun _ _ hu hv => h _ _ (hu.pre_base he.symm) (hv.pre_base he.symm)

/-- Composition has no homomorphic root; disjoint reductions commute with exact
output bags, including arbitrary expansion and arbitrary retained factors. -/
theorem disjoint_compose_reductions_joined (source u v a a' b b' : Term V)
    (rest : Multiset (BaseClass V)) (ha : ModuloStep a a') (hb : ModuloStep b b')
    (hs : source.composeFactors = a.composeFactors + (b.composeFactors + rest))
    (hu : u.composeFactors = a'.composeFactors + (b.composeFactors + rest))
    (hv : v.composeFactors = a.composeFactors + (b'.composeFactors + rest)) :
    ModuloStep source u ∧ ModuloStep source v ∧ JoinModulo u v := by
  have hj : JoinModulo (.binary .compose a' b) (.binary .compose a b') :=
    ⟨.binary .compose a' b', .single (hb.context (.binaryRight .compose a' .hole)),
      .single (ha.context (.binaryLeft .compose .hole b'))⟩
  refine ⟨ha.of_compose_factors (b.composeFactors + rest) hs hu, ?_, ?_⟩
  · apply (hb.context (.binaryRight .compose a .hole)).of_compose_factors rest
    · simpa only [Context.fill, Term.composeFactors, Multiset.add_assoc] using hs
    · simpa only [Context.fill, Term.composeFactors, Multiset.add_assoc] using hv
  · exact hj.of_compose_factors rest
      (by simpa only [Term.composeFactors, Multiset.add_assoc] using hu)
      (by simpa only [Term.composeFactors, Multiset.add_assoc] using hv)

/-- This selected-factor local-confluence obligation stays explicit. -/
def ComposeFactorsLocallyConfluent (source : Term V) : Prop :=
  ∀ a b c : Term V, a.composeFactors = {a.baseClass} → a.baseClass ∈ source.composeFactors →
    ModuloStep a b → ModuloStep a c → JoinModulo b c

theorem compose_factor_peaks_joined {source u v : Term V}
    (hl : ComposeFactorsLocallyConfluent source)
    (hu : ComposeFactorStep source u) (hv : ComposeFactorStep source v) : JoinModulo u v := by
  obtain ⟨a, a', rx, ha, haa, hs, hu⟩ := hu
  obtain ⟨b, b', ry, hb, hbb, hs', hv⟩ := hv
  rcases singleton_selection_cases source.composeFactors a.baseClass b.baseClass rx ry hs hs' with
    ⟨he, hr⟩ | ⟨rest, hrx, hry⟩
  · have hba : ModuloStep a b' := hbb.pre_base ((baseClass_eq_iff _ _).mp he)
    have hm : a.baseClass ∈ source.composeFactors := by rw [hs]; simp
    exact (hl a a' b' ha hm haa hba).of_compose_factors rx hu (by simpa only [hr] using hv)
  · exact (disjoint_compose_reductions_joined source u v a a' b b' rest haa hbb
      (by simpa only [ha, hb, hrx] using hs)
      (by simpa only [hb, hrx] using hu) (by
        rw [hv, hry, ← Multiset.add_assoc, Multiset.add_comm b'.composeFactors, Multiset.add_assoc, ha])).2.2

/-- Every composition-context peak is accounted for once the factor-local premise
is supplied. This does not discharge that premise for arbitrary terms. -/
theorem locally_confluent_at_of_compose_factors (source : Term V)
    (hl : ComposeFactorsLocallyConfluent source) : LocallyConfluentAt source :=
  fun _ _ hu hv => compose_factor_peaks_joined hl hu.compose_factor hv.compose_factor

/-- A representative-based interface for supplying the explicit factor-local premise. -/
theorem compose_factors_local_of_representatives (source : Term V)
    (h : ∀ q ∈ source.composeFactors, ∃ a : Term V, a.baseClass = q ∧ LocallyConfluentAt a) :
    ComposeFactorsLocallyConfluent source := by
  intro a b c _ hm hab hac
  obtain ⟨t, ht, hl⟩ := h a.baseClass hm
  exact (hl.of_base ((baseClass_eq_iff _ _).mp ht.symm)) b c hab hac

/-- An irreducible factor family has no composite step; no root matcher is used. -/
theorem irreducible_of_compose_factors (source : Term V)
    (h : ∀ a : Term V, a.composeFactors = {a.baseClass} →
      a.baseClass ∈ source.composeFactors → Irreducible a) : Irreducible source := by
  intro t ht
  obtain ⟨a, b, rest, ha, hab, hs, _⟩ := ht.compose_factor
  have hm : a.baseClass ∈ source.composeFactors := by rw [hs]; simp
  exact h a ha hm b hab

end ExplainableCrypto.Helios.Symbolic
