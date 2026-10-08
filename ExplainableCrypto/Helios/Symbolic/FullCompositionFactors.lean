import ExplainableCrypto.Helios.Symbolic.MinimumDestructorTransfer

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Full-E classes for metatheory accounting, not an executable equality test. -/
def fullSetoid (V : Type) : Setoid (Term V) where
  r := EqE
  iseqv := ⟨EqE.refl, EqE.symm, EqE.trans⟩
abbrev FullClass (V : Type) := Quotient (fullSetoid V)
def Term.fullClass (t : Term V) : FullClass V := Quotient.mk (fullSetoid V) t

theorem fullClass_eq_iff (a b : Term V) : a.fullClass = b.fullClass ↔ EqE a b :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound (s := fullSetoid V) h⟩

/-- Flatten raw outer composition, retaining each factor's full-E class. -/
def Term.composeValueFactors : Term V → Multiset (FullClass V)
  | .binary .compose a b => a.composeValueFactors + b.composeValueFactors
  | t => {t.fullClass}

/-- An indivisible composition factor has no composition E-value. -/
def FullClass.ComposeAtom (q : FullClass V) : Prop :=
  ∀ a b : Term V, q ≠ (Term.binary .compose a b).fullClass

def Term.AtomicComposeFactors (t : Term V) : Prop :=
  ∀ q ∈ t.composeValueFactors, q.ComposeAtom

private def baseToFull : BaseClass V → FullClass V :=
  Quotient.lift Term.fullClass (fun _ _ h => Quotient.sound (s := fullSetoid V) h.sound)

private theorem baseToFull_baseClass (t : Term V) :
    baseToFull t.baseClass = t.fullClass := rfl

private theorem factors_map (t : Term V) :
    t.composeValueFactors = t.composeFactors.map baseToFull := by
  induction t with
  | binary f a b ha hb => cases f <;> simp_all [Term.composeValueFactors, Term.composeFactors, baseToFull_baseClass]
  | _ => simp [Term.composeValueFactors, Term.composeFactors, baseToFull_baseClass]

theorem BaseEq.compose_value_factors {a b : Term V} (he : BaseEq a b) :
    a.composeValueFactors = b.composeValueFactors := by
  rw [factors_map, factors_map, he.compose_factors]

/-- A term without literal compose syntax contributes exactly one full-E class. -/
theorem Term.composeValueFactors_singleton {t : Term V}
    (h : ∀ a b, t ≠ .binary .compose a b) : t.composeValueFactors = {t.fullClass} := by
  cases t with
  | binary f a b => cases f <;> first | rfl | exact False.elim (h a b rfl)
  | _ => rfl

/-- A modulo step cannot split a semantically indivisible factor. Reducible
factors remain permitted, and their full-E classes retain multiplicity. -/
theorem ModuloStep.compose_value_factors {a b : Term V} (h : ModuloStep a b)
    (ha : a.AtomicComposeFactors) : a.composeValueFactors = b.composeValueFactors := by
  obtain ⟨x, y, rest, _, hxy, hs, ht⟩ := h.compose_factor
  have hx : x.fullClass.ComposeAtom := ha x.fullClass (by
    rw [factors_map, hs]
    simp [baseToFull_baseClass])
  have hy : y.composeValueFactors = {y.fullClass} := Term.composeValueFactors_singleton (by
    intro u v he
    subst y
    exact hx u v ((fullClass_eq_iff _ _).mpr hxy.sound))
  rw [factors_map a, factors_map b, hs, ht, Multiset.map_add, Multiset.map_add, Multiset.map_singleton]
  rw [← factors_map y]
  change {x.fullClass} + rest.map baseToFull = y.composeValueFactors + rest.map baseToFull
  rw [hy, (fullClass_eq_iff _ _).mpr hxy.sound]

/-- Actual paths preserve the factor bag when all initial factors are semantic
composition atoms. No hypothesis on intermediate normal forms is required. -/
theorem ReducesModulo.compose_value_factors {a b : Term V} (h : ReducesModulo a b)
    (ha : a.AtomicComposeFactors) : a.composeValueFactors = b.composeValueFactors := by
  revert ha
  induction h with
  | base he => exact fun _ => he.compose_value_factors
  | head hs _ ih =>
    intro ha
    have he := hs.compose_value_factors ha
    exact he.trans (ih (by intro q hq; exact ha q (he.symm ▸ hq)))

section Reconstruction
local instance fullComposeSemigroup : CommSemigroup (FullClass V) where
  mul a b := Quotient.liftOn₂ a b (fun a b => (Term.binary .compose a b).fullClass)
    (fun _ _ _ _ ha hb => Quotient.sound (s := fullSetoid V) (.binary .compose ha hb))
  mul_assoc a b c := Quotient.inductionOn₃ a b c fun a b c =>
    Quotient.sound (s := fullSetoid V) (.equation (.assoc .compose trivial a b c))
  mul_comm a b := Quotient.inductionOn₂ a b fun a b =>
    Quotient.sound (s := fullSetoid V) (.equation (.comm .compose trivial a b))

private def composeProduct (s : Multiset (FullClass V)) : WithOne (FullClass V) :=
  (s.map fun x : FullClass V => (x : WithOne (FullClass V))).prod

private theorem composeProduct_add (a b : Multiset (FullClass V)) :
    composeProduct (a+b) = composeProduct a * composeProduct b := by
  simp [composeProduct, Multiset.prod_add]

private theorem reconstruct (t : Term V) : composeProduct t.composeValueFactors =
    (t.fullClass : WithOne (FullClass V)) := by
  induction t with
  | binary f a b ha hb =>
    cases f <;> first
      | exact (by rw [Term.composeValueFactors, composeProduct_add, ha, hb]; rfl)
      | simp [Term.composeValueFactors, composeProduct]
  | _ => simp [Term.composeValueFactors, composeProduct]

/-- Equal full-E factor bags reconstruct equal terms without an atom premise.
The fold's auxiliary identity is not added to the term language. -/
theorem eqE_of_compose_value_factors {a b : Term V}
    (he : a.composeValueFactors = b.composeValueFactors) : EqE a b := by
  have hp := congrArg composeProduct he
  rw [reconstruct a, reconstruct b] at hp
  exact (fullClass_eq_iff _ _).mp (WithOne.coe_injective hp)
end Reconstruction

/-- Full-E equality of compositions with indivisible semantic factors is exactly
multiset equality of factor E-classes. Both no-composition premises are explicit. -/
theorem eqE_iff_compose_value_factors (a b : Term V)
    (ha : a.AtomicComposeFactors) (hb : b.AtomicComposeFactors) :
    EqE a b ↔ a.composeValueFactors = b.composeValueFactors := by
  refine ⟨?_, eqE_of_compose_value_factors⟩
  intro he
  obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp he
  exact (hl.compose_value_factors ha).trans (hr.compose_value_factors hb).symm

end ExplainableCrypto.Helios.Symbolic
