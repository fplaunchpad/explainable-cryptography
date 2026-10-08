import ExplainableCrypto.Helios.Symbolic.SourceElectionConditionalLocation

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- A left inverse on a complete term modulo full E. No literal support name
is discarded by this definition; E itself justifies every discarded field. -/
def Term.NameRetracts (t : Term V) (f g : Nat → Nat) : Prop :=
  EqE ((t.mapNames f).mapNames g) t

theorem Term.NameRetracts.of_inverse (t : Term V) (e : Nat ≃ Nat) :
    t.NameRetracts e e.symm := by
  unfold NameRetracts
  rw [Term.mapNames_inverse]
  exact .refl _

theorem Term.NameRetracts.congr {t u : Term V} {f g : Nat → Nat}
    (h : t.NameRetracts f g) (he : EqE t u) : u.NameRetracts f g :=
  ((he.mapNames f).mapNames g).symm.trans (h.trans he)

theorem EqE.mapNames_iff_of_retractions (a b : Term V) (f g : Nat → Nat)
    (ha : a.NameRetracts f g) (hb : b.NameRetracts f g) :
    EqE (a.mapNames f) (b.mapNames f) ↔ EqE a b :=
  ⟨fun h => ha.symm.trans ((h.mapNames g).trans hb),fun h => h.mapNames f⟩

theorem Term.NameRetracts.unary (op : Unary) {t : Term V} {f g : Nat → Nat}
    (h : t.NameRetracts f g) : (Term.unary op t).NameRetracts f g := EqE.unary op h

theorem Term.NameRetracts.binary (op : Binary) {a b : Term V} {f g : Nat → Nat}
    (ha : a.NameRetracts f g) (hb : b.NameRetracts f g) :
    (Term.binary op a b).NameRetracts f g := EqE.binary op ha hb

theorem Term.NameRetracts.ternary (op : Ternary) {a b c : Term V} {f g : Nat → Nat}
    (ha : a.NameRetracts f g) (hb : b.NameRetracts f g) (hc : c.NameRetracts f g) :
    (Term.ternary op a b c).NameRetracts f g := EqE.ternary op ha hb hc

theorem Term.NameRetracts.spk {a b c d : Term V} {f g : Nat → Nat}
    (ha : a.NameRetracts f g) (hb : b.NameRetracts f g)
    (hc : c.NameRetracts f g) (hd : d.NameRetracts f g) :
    (Term.spk a b c d).NameRetracts f g := EqE.spk ha hb hc hd

namespace Historical.General.Source.Formula

/-- All equality/disequality operands round-trip modulo E, retaining polarity
and conjunction. This is stronger than mere equality of truth values. -/
def NameRetracts (p : Formula V) (f g : Nat → Nat) : Prop :=
  EquivE ((p.mapNames f).mapNames g) p

theorem NameRetracts.of_inverse (p : Formula V) (e : Nat ≃ Nat) :
    p.NameRetracts e e.symm := by
  unfold NameRetracts
  have hi : (e.symm ∘ e : Nat → Nat) = id := by funext n; exact e.symm_apply_apply n
  rw [Formula.mapNames_comp,hi,Formula.mapNames_id]
  exact .refl _

theorem NameRetracts.congr {p q : Formula V} {f g : Nat → Nat}
    (h : p.NameRetracts f g) (he : EquivE p q) : q.NameRetracts f g :=
  ((he.mapNames f).mapNames g).symm.trans (h.trans he)

theorem NameRetracts.holds_mapNames {p : Formula Empty} {f g : Nat → Nat}
    (h : p.NameRetracts f g) :
    (p.mapNames f).Holds Empty.elim ↔ p.Holds Empty.elim := by
  have hv : (Empty.elim : Empty → Ground) = Term.var := by funext v; exact v.elim
  induction p with
  | equal a b =>
    cases h with
    | equal ha hb =>
      simpa only [Formula.mapNames,Holds,hv,Term.subst_var] using
        EqE.mapNames_iff_of_retractions a b f g ha hb
  | unequal a b =>
    cases h with
    | unequal ha hb =>
      simpa only [Formula.mapNames,Holds,hv,Term.subst_var] using
        not_congr (EqE.mapNames_iff_of_retractions a b f g ha hb)
  | both p q hp hq =>
    cases h with
    | both ha hb => exact and_congr (hp ha) (hq hb)

end Historical.General.Source.Formula
end ExplainableCrypto.Helios.Symbolic
