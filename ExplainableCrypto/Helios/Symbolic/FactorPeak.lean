import ExplainableCrypto.Helios.Symbolic.FactorStepCoverage

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Classify two single-occurrence selections while retaining both exact residuals.
Equal values may have different position realizations; no unique position is claimed. -/
theorem singleton_selection_cases {α : Type} (source : Multiset α) (x y : α)
    (rx ry : Multiset α) (hx : source = {x} + rx) (hy : source = {y} + ry) :
    (x = y ∧ rx = ry) ∨ ∃ rest, rx = {y} + rest ∧ ry = {x} + rest := by
  classical
  by_cases he : x = y
  · subst y
    exact Or.inl ⟨rfl, Multiset.add_right_inj.mp (hx.symm.trans hy)⟩
  · have hm : y ∈ rx := by
      have hm : y ∈ source := by rw [hy]; simp
      rw [hx] at hm
      simpa [Ne.symm he] using hm
    obtain ⟨rest, hrest⟩ := Multiset.exists_cons_of_mem hm
    have hrx : rx = {y} + rest := by simpa only [Multiset.singleton_add] using hrest
    refine Or.inr ⟨rest, hrx, ?_⟩
    have hh := hy.symm.trans hx
    rw [hrx, ← Multiset.add_assoc, Multiset.add_comm ({x} : Multiset α), Multiset.add_assoc] at hh
    exact Multiset.add_right_inj.mp hh

/-- Two disjoint subterms can reduce independently, with arbitrary expanding
outputs and an arbitrary outer remainder. The branch bags specify both choices. -/
theorem disjoint_factor_reductions_joined (source u v a a' b b' : Term V)
    (rest : Multiset (BaseClass V)) (ha : ModuloStep a a') (hb : ModuloStep b b')
    (hs : source.mulFactors = a.mulFactors + (b.mulFactors + rest))
    (hu : u.mulFactors = a'.mulFactors + (b.mulFactors + rest))
    (hv : v.mulFactors = a.mulFactors + (b'.mulFactors + rest)) :
    ModuloStep source u ∧ ModuloStep source v ∧ JoinModulo u v := by
  have hj : JoinModulo (.binary .mul a' b) (.binary .mul a b') :=
    ⟨.binary .mul a' b', .single (hb.context (.binaryRight .mul a' .hole)),
      .single (ha.context (.binaryLeft .mul .hole b'))⟩
  refine ⟨ha.of_factors (b.mulFactors + rest) hs hu, ?_, ?_⟩
  · apply (hb.context (.binaryRight .mul a .hole)).of_factors rest
    · simpa only [Context.fill, Term.mulFactors, Multiset.add_assoc] using hs
    · simpa only [Context.fill, Term.mulFactors, Multiset.add_assoc] using hv
  · exact hj.of_factors rest
      (by simpa only [Term.mulFactors, Multiset.add_assoc] using hu)
      (by simpa only [Term.mulFactors, Multiset.add_assoc] using hv)

/-- Local confluence only for single-factor representatives present in this source.
This remains a premise; the factor decomposition alone does not prove it. -/
def FactorsLocallyConfluent (source : Term V) : Prop :=
  ∀ a b c : Term V, a.mulFactors = {a.baseClass} → a.baseClass ∈ source.mulFactors →
    ModuloStep a b → ModuloStep a c → JoinModulo b c

/-- Exhaustive factor/factor analysis, with the same-factor join explicitly required. -/
theorem factor_peaks_joined_of_factor_local {source u v : Term V}
    (hl : FactorsLocallyConfluent source) (hu : FactorStep source u) (hv : FactorStep source v) :
    JoinModulo u v := by
  obtain ⟨a, a', rx, ha, haa, hs, hu⟩ := hu
  obtain ⟨b, b', ry, hb, hbb, hs', hv⟩ := hv
  rcases singleton_selection_cases source.mulFactors a.baseClass b.baseClass rx ry hs hs' with
    ⟨he, hr⟩ | ⟨rest, hrx, hry⟩
  · have hba : ModuloStep a b' := hbb.pre_base ((baseClass_eq_iff _ _).mp he)
    have hm : a.baseClass ∈ source.mulFactors := by rw [hs]; simp
    exact (hl a a' b' ha hm haa hba).of_factors rx hu (by simpa only [hr] using hv)
  · exact (disjoint_factor_reductions_joined source u v a a' b b' rest haa hbb
      (by simpa only [ha, hb, hrx] using hs)
      (by simpa only [hb, hrx] using hu) (by
        rw [hv, hry, ← Multiset.add_assoc, Multiset.add_comm b'.mulFactors, Multiset.add_assoc, ha])).2.2

/-- Once all single-factor peaks occurring in a source join, all its peaks join. -/
theorem modulo_peaks_joined_of_factor_local {source u v : Term V}
    (hl : FactorsLocallyConfluent source) (hu : ModuloStep source u) (hv : ModuloStep source v) :
    JoinModulo u v := by
  rcases hu.factor_cases with hu | hu
  · exact outer_fusion_modulo_peak_joined hu hv
  rcases hv.factor_cases with hv | hv
  · exact (outer_fusion_modulo_peak_joined hv hu.to_modulo).symm
  · exact factor_peaks_joined_of_factor_local hl hu hv

/-- The singleton-source restriction used by the confluence decomposition. -/
def SingleFactorLocalConfluent (V : Type) : Prop :=
  ∀ a b c : Term V, a.mulFactors = {a.baseClass} →
    ModuloStep a b → ModuloStep a c → JoinModulo b c

/-- Outer-product analysis reduces whole-theory local confluence to singleton
sources. `GlobalConfluence.lean` subsequently discharges the right-hand proposition. -/
theorem local_confluence_iff_single_factor :
    LocalConfluentModulo V ↔ SingleFactorLocalConfluent V := by
  constructor
  · intro h a b c _ hab hac
    exact h a b c hab hac
  · intro h source u v hu hv
    exact modulo_peaks_joined_of_factor_local (fun a b c ha _ => h a b c ha) hu hv

end ExplainableCrypto.Helios.Symbolic
