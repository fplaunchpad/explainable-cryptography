import ExplainableCrypto.Helios.Symbolic.FullCompositionFactors

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Flatten raw outer addition, retaining numeric presence and full-E atom classes. -/
def Term.addValueSummary : Term V → AddSummary (FullClass V)
  | .const .zero => .number 0
  | .const .one => .number 1
  | .binary .add a b => a.addValueSummary.combine b.addValueSummary
  | t => .atom t.fullClass

/-- A nonnumeric addition atom cannot reveal addition or either numeric constant. -/
def FullClass.AddAtom (q : FullClass V) : Prop :=
  (∀ a b : Term V, q ≠ (Term.binary .add a b).fullClass) ∧
  q ≠ (Term.const .zero).fullClass ∧ q ≠ (Term.const .one).fullClass

def Term.AtomicAddFactors (t : Term V) : Prop :=
  ∀ q ∈ t.addValueSummary.atoms, q.AddAtom

private def baseToFull : BaseClass V → FullClass V :=
  Quotient.lift Term.fullClass (fun _ _ h => Quotient.sound (s := fullSetoid V) h.sound)
private theorem baseToFull_baseClass (t : Term V) :
    baseToFull t.baseClass = t.fullClass := rfl

private def summaryMap (s : AddSummary (BaseClass V)) : AddSummary (FullClass V) :=
  ⟨s.atoms.map baseToFull, s.numeric⟩
private theorem summaryMap_combine (a b : AddSummary (BaseClass V)) :
    summaryMap (a.combine b) = (summaryMap a).combine (summaryMap b) := by
  simp [summaryMap, AddSummary.combine]
private theorem summary_map (t : Term V) : t.addValueSummary = summaryMap t.addSummary := by
  induction t with
  | binary f a b ha hb =>
    cases f <;> simp_all [Term.addValueSummary, Term.addSummary, summaryMap, AddSummary.combine,
      AddSummary.atom, baseToFull_baseClass]
  | const c => cases c <;> rfl
  | _ => rfl

theorem BaseEq.add_value_summary {a b : Term V} (he : BaseEq a b) :
    a.addValueSummary = b.addValueSummary := by
  rw [summary_map, summary_map, he.add_summary]

/-- Raw non-additive, nonnumeric syntax contributes exactly one atom. -/
theorem Term.addValueSummary_atom {t : Term V}
    (ha : ∀ a b, t ≠ .binary .add a b)
    (hz : t ≠ .const .zero) (ho : t ≠ .const .one) :
    t.addValueSummary = .atom t.fullClass := by
  cases t with
  | binary f a b => cases f <;> first | rfl | exact False.elim (ha a b rfl)
  | const c => cases c <;> first | rfl | exact False.elim (hz rfl) | exact False.elim (ho rfl)
  | _ => rfl

/-- Semantic atomicity prevents a reducing atom from exposing numeric material
or more than one summand. The atom itself need not be irreducible. -/
theorem ModuloStep.add_value_summary {a b : Term V} (h : ModuloStep a b)
    (ha : a.AtomicAddFactors) : a.addValueSummary = b.addValueSummary := by
  obtain ⟨x, y, rest, _, hxy, hs, ht⟩ := h.add_factor
  have hx : x.fullClass.AddAtom := ha x.fullClass (by
    rw [summary_map, hs]
    simp [summaryMap, AddSummary.combine, AddSummary.atom, baseToFull_baseClass])
  have he := (fullClass_eq_iff _ _).mpr hxy.sound
  have hy : y.addValueSummary = .atom y.fullClass := Term.addValueSummary_atom
    (by intro u v h; subst y; exact hx.1 u v he)
    (by intro h; subst y; exact hx.2.1 he)
    (by intro h; subst y; exact hx.2.2 he)
  rw [summary_map a, summary_map b, hs, ht, summaryMap_combine, summaryMap_combine, ← summary_map y]
  change (AddSummary.atom x.fullClass).combine (summaryMap rest) = y.addValueSummary.combine (summaryMap rest)
  rw [hy, he]

theorem ReducesModulo.add_value_summary {a b : Term V} (h : ReducesModulo a b)
    (ha : a.AtomicAddFactors) : a.addValueSummary = b.addValueSummary := by
  revert ha
  induction h with
  | base he => exact fun _ => he.add_value_summary
  | head hs _ ih =>
    intro ha
    have he := hs.add_value_summary ha
    exact he.trans (ih (by intro q hq; exact ha q (by simpa only [he] using hq)))

section FullAdditionFold

/-- The fold uses addition only in this section; exported quotient multiplication
continues to denote multiplication. -/
local instance fullAdditionSemigroup : CommSemigroup (FullClass V) where
  mul a b := Quotient.liftOn₂ a b (fun a b => (Term.binary .add a b).fullClass)
    (fun _ _ _ _ ha hb => Quotient.sound (s := fullSetoid V) (.binary .add ha hb))
  mul_assoc a b c := Quotient.inductionOn₃ a b c fun a b c =>
    Quotient.sound (s := fullSetoid V) (.equation (.assoc .add trivial a b c))
  mul_comm a b := Quotient.inductionOn₂ a b fun a b =>
    Quotient.sound (s := fullSetoid V) (.equation (.comm .add trivial a b))

private def numericProduct : Option Nat → WithOne (FullClass V)
  | none => 1
  | some n => ((addNumeral (V := V) n).fullClass : WithOne (FullClass V))

private theorem numericProduct_combine (a b : Option Nat) :
    numericProduct (V := V) (numericAdd a b) = numericProduct a * numericProduct b := by
  cases a with
  | none => cases b <;> simp [numericAdd, numericProduct]
  | some n =>
    cases b with
    | none => simp [numericAdd, numericProduct]
    | some m =>
      exact congrArg (fun q : FullClass V => (q : WithOne (FullClass V)))
        ((fullClass_eq_iff _ _).mpr (addNumerals_combine n m).sound).symm

private def summaryProduct (s : AddSummary (FullClass V)) : WithOne (FullClass V) :=
  (s.atoms.map fun q : FullClass V => (q : WithOne (FullClass V))).prod * numericProduct s.numeric

private theorem summaryProduct_combine (a b : AddSummary (FullClass V)) :
    summaryProduct (a.combine b) = summaryProduct a * summaryProduct b := by
  simp only [summaryProduct, AddSummary.combine, Multiset.map_add, Multiset.prod_add, numericProduct_combine]
  ac_rfl

private theorem summaryProduct_atom (q : FullClass V) :
    summaryProduct (.atom q) = (q : WithOne (FullClass V)) := by
  simp [summaryProduct, AddSummary.atom, numericProduct]

private theorem summaryProduct_number (n : Nat) :
    summaryProduct (V := V) (.number n) = ((addNumeral (V := V) n).fullClass : WithOne (FullClass V)) := by
  simp [summaryProduct, AddSummary.number, numericProduct]

private theorem addSummary_reconstruct (t : Term V) :
    summaryProduct t.addValueSummary = (t.fullClass : WithOne (FullClass V)) := by
  induction t with
  | name => exact summaryProduct_atom _
  | var => exact summaryProduct_atom _
  | const c =>
    cases c with
    | zero => exact summaryProduct_number 0
    | one =>
      exact (summaryProduct_number 1).trans
        (congrArg (fun q : FullClass V => (q : WithOne (FullClass V)))
          ((fullClass_eq_iff _ _).mpr (.equation .zero_one)))
    | ok => exact summaryProduct_atom _
    | bottom => exact summaryProduct_atom _
  | unary => exact summaryProduct_atom _
  | binary f a b ha hb =>
    cases f <;> first
      | exact (by rw [Term.addValueSummary, summaryProduct_combine, ha, hb]; rfl)
      | exact summaryProduct_atom _
  | ternary => exact summaryProduct_atom _
  | spk => exact summaryProduct_atom _


/-- Equal summaries reconstruct equal terms even if some recorded atoms can
reduce to numeric or additive values. The fold identity stays outside the syntax. -/
theorem eqE_of_add_value_summary {a b : Term V}
    (he : a.addValueSummary = b.addValueSummary) : EqE a b := by
  have hp := congrArg summaryProduct he
  rw [addSummary_reconstruct a, addSummary_reconstruct b] at hp
  exact (fullClass_eq_iff _ _).mp (WithOne.coe_injective hp)

theorem Term.addValueSummary_ne_empty (t : Term V) : t.addValueSummary ≠ .empty := by
  intro he
  have hp := congrArg summaryProduct he
  rw [addSummary_reconstruct t] at hp
  simp [summaryProduct, AddSummary.empty, numericProduct] at hp
end FullAdditionFold

/-- Exact full-E addition equality retains both atom multiplicity and the
optional numeric count. Atomicity is required on both supplied terms. -/
theorem eqE_iff_add_value_summary (a b : Term V)
    (ha : a.AtomicAddFactors) (hb : b.AtomicAddFactors) :
    EqE a b ↔ a.addValueSummary = b.addValueSummary := by
  refine ⟨?_, eqE_of_add_value_summary⟩
  intro he
  obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp he
  exact (hl.add_value_summary ha).trans (hr.add_value_summary hb).symm

end ExplainableCrypto.Helios.Symbolic
