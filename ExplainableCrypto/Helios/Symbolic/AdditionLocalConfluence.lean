import ExplainableCrypto.Helios.Symbolic.AdditionSelection
import ExplainableCrypto.Helios.Symbolic.ComposeLocalConfluence

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Addition has no homomorphic root; disjoint reductions commute with exact
output summaries, including arbitrary expansion and arbitrary retained factors. -/
theorem disjoint_add_reductions_joined (source u v a a' b b' : Term V)
    (rest : AddSummary (BaseClass V)) (ha : ModuloStep a a') (hb : ModuloStep b b')
    (hs : source.addSummary = a.addSummary.combine (b.addSummary.combine rest))
    (hu : u.addSummary = a'.addSummary.combine (b.addSummary.combine rest))
    (hv : v.addSummary = a.addSummary.combine (b'.addSummary.combine rest)) :
    ModuloStep source u ∧ ModuloStep source v ∧ JoinModulo u v := by
  have hj : JoinModulo (.binary .add a' b) (.binary .add a b') :=
    ⟨.binary .add a' b', .single (hb.context (.binaryRight .add a' .hole)),
      .single (ha.context (.binaryLeft .add .hole b'))⟩
  refine ⟨ha.of_add_summaries (b.addSummary.combine rest) hs hu, ?_, ?_⟩
  · apply (hb.context (.binaryRight .add a .hole)).of_add_summaries rest
    · simpa only [Context.fill, Term.addSummary, AddSummary.combine_assoc] using hs
    · simpa only [Context.fill, Term.addSummary, AddSummary.combine_assoc] using hv
  · exact hj.of_add_summaries rest
      (by simpa only [Term.addSummary, AddSummary.combine_assoc] using hu)
      (by simpa only [Term.addSummary, AddSummary.combine_assoc] using hv)

/-- This selected-factor local-confluence obligation stays explicit. -/
def AddFactorsLocallyConfluent (source : Term V) : Prop :=
  ∀ a b c : Term V, a.addSummary = (.atom a.baseClass) → a.baseClass ∈ source.addSummary.atoms →
    ModuloStep a b → ModuloStep a c → JoinModulo b c

theorem add_factor_peaks_joined {source u v : Term V}
    (hl : AddFactorsLocallyConfluent source)
    (hu : AddFactorStep source u) (hv : AddFactorStep source v) : JoinModulo u v := by
  obtain ⟨a, a', rx, ha, haa, hs, hu⟩ := hu
  obtain ⟨b, b', ry, hb, hbb, hs', hv⟩ := hv
  rcases AddSummary.atom_selection_cases source.addSummary a.baseClass b.baseClass rx ry hs hs' with
    ⟨he, hr⟩ | ⟨rest, hrx, hry⟩
  · have hba : ModuloStep a b' := hbb.pre_base ((baseClass_eq_iff _ _).mp he)
    have hm : a.baseClass ∈ source.addSummary.atoms := by rw [hs]; simp [AddSummary.combine, AddSummary.atom]
    exact (hl a a' b' ha hm haa hba).of_add_summaries rx hu (by simpa only [hr] using hv)
  · exact (disjoint_add_reductions_joined source u v a a' b b' rest haa hbb
      (by simpa only [ha, hb, hrx] using hs)
      (by simpa only [hb, hrx] using hu) (by
        rw [hv, hry, ← AddSummary.combine_assoc, AddSummary.combine_comm b'.addSummary, AddSummary.combine_assoc, ha])).2.2

/-- Every addition-context peak is accounted for once the factor-local premise
is supplied. This does not discharge that premise for arbitrary terms. -/
theorem locally_confluent_at_of_add_summaries (source : Term V)
    (hl : AddFactorsLocallyConfluent source) : LocallyConfluentAt source :=
  fun _ _ hu hv => add_factor_peaks_joined hl hu.add_factor hv.add_factor

/-- A representative-based interface for supplying the explicit factor-local premise. -/
theorem add_summaries_local_of_representatives (source : Term V)
    (h : ∀ q ∈ source.addSummary.atoms, ∃ a : Term V, a.baseClass = q ∧ LocallyConfluentAt a) :
    AddFactorsLocallyConfluent source := by
  intro a b c _ hm hab hac
  obtain ⟨t, ht, hl⟩ := h a.baseClass hm
  exact (hl.of_base ((baseClass_eq_iff _ _).mp ht.symm)) b c hab hac

/-- An irreducible factor family has no composite step; no root matcher is used. -/
theorem irreducible_of_add_summaries (source : Term V)
    (h : ∀ a : Term V, a.addSummary = (.atom a.baseClass) →
      a.baseClass ∈ source.addSummary.atoms → Irreducible a) : Irreducible source := by
  intro t ht
  obtain ⟨a, b, rest, ha, hab, hs, _⟩ := ht.add_factor
  have hm : a.baseClass ∈ source.addSummary.atoms := by rw [hs]; simp [AddSummary.combine, AddSummary.atom]
  exact h a ha hm b hab

/-- A summary containing only its numeric part admits no modulo step. -/
theorem irreducible_of_add_atoms_empty (source : Term V)
    (h : source.addSummary.atoms = 0) : Irreducible source := by
  apply irreducible_of_add_summaries
  intro a _ hm
  rw [h] at hm
  exact False.elim (Multiset.notMem_zero _ hm)

theorem addNumeral_irreducible (n : Nat) : Irreducible (addNumeral (V := V) n) :=
  irreducible_of_add_atoms_empty _ (by rw [addNumeral_summary]; rfl)

end ExplainableCrypto.Helios.Symbolic
