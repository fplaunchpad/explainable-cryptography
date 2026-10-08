import ExplainableCrypto.Helios.Symbolic.SourceGuardRetractions

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type}

theorem Term.NameRetracts.of_fixed_support (t : Term V) (f g : Nat → Nat)
    (h : ∀ n ∈ t.nameSupport, g (f n) = n) : t.NameRetracts f g := by
  unfold NameRetracts
  rw [Term.mapNames_comp,t.mapNames_congr (g ∘ f) id h,Term.mapNames_id]
  exact .refl _

theorem Term.NameRetracts.subst {t : Term V} {f g : Nat → Nat}
    (h : t.NameRetracts f g) (σ : V → Term W) (hs : ∀ v, (σ v).NameRetracts f g) :
    (t.subst σ).NameRetracts f g := by
  unfold NameRetracts at *
  rw [Term.mapNames_subst,Term.mapNames_subst]
  exact (((t.mapNames f).mapNames g).subst_congr _ σ hs).trans (h.subst σ)

namespace Historical.General.Source.Formula

theorem NameRetracts.subst {p : Formula V} {f g : Nat → Nat}
    (h : p.NameRetracts f g) (σ : V → Term W) (hs : ∀ v, (σ v).NameRetracts f g) :
    (p.subst σ).NameRetracts f g := by
  unfold NameRetracts at *
  rw [Formula.mapNames_subst,Formula.mapNames_subst]
  exact (((p.mapNames f).mapNames g).subst_equivE _ σ hs).trans (h.subst σ)

theorem NameRetracts.holds_mapped_environment {p : Formula V} {f g : Nat → Nat}
    (h : p.NameRetracts f g) (env : V → Ground) (he : ∀ v, (env v).NameRetracts f g) :
    (p.mapNames f).Holds (fun v => (env v).mapNames f) ↔ p.Holds env := by
  have hh := (h.subst env he).holds_mapNames
  rw [Formula.mapNames_subst,Formula.holds_subst,Formula.holds_subst] at hh
  have hi (t : Ground) : t.subst Empty.elim = t := by
    have hv : (Empty.elim : Empty → Ground) = Term.var := by funext v; exact v.elim
    rw [hv,Term.subst_var]
  simpa only [hi] using hh

end Historical.General.Source.Formula
end ExplainableCrypto.Helios.Symbolic
