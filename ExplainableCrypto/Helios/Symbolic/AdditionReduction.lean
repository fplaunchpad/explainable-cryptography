import ExplainableCrypto.Helios.Symbolic.AdditionRepresentatives
import ExplainableCrypto.Helios.Symbolic.Confluence

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Lift a specified modulo step through an arbitrary outer addition-factor remainder.
The exact endpoint summaries retain multiplicity; empty remainders need no unit. -/
theorem ModuloStep.of_add_summaries {a b u v : Term V} (h : ModuloStep a b)
    (rest : AddSummary (BaseClass V))
    (hu : u.addSummary = a.addSummary.combine rest)
    (hv : v.addSummary = b.addSummary.combine rest) : ModuloStep u v := by
  by_cases hr : rest = .empty
  · subst rest
    exact (h.pre_base ((baseEq_iff_addSummary _ _).mpr (by simpa using hu))).post_base
      ((baseEq_iff_addSummary _ _).mpr (by simpa using hv.symm))
  · have hsub : rest.atoms ≤ u.addSummary.atoms := by rw [hu]; exact Multiset.le_add_left _ _
    obtain ⟨tail, htail⟩ := u.add_subsummary_representable rest hsub hr
    exact ((h.context (.binaryLeft .add .hole tail)).pre_base
      ((baseEq_iff_addSummary _ _).mpr (by simpa only [Context.fill, Term.addSummary, htail] using hu))).post_base
      ((baseEq_iff_addSummary _ _).mpr (by simpa only [Context.fill, Term.addSummary, htail] using hv.symm))

/-- Lift a join through arbitrary specified endpoint factor summaries. -/
theorem JoinModulo.of_add_summaries {a b u v : Term V} (h : JoinModulo a b)
    (rest : AddSummary (BaseClass V))
    (hu : u.addSummary = a.addSummary.combine rest)
    (hv : v.addSummary = b.addSummary.combine rest) : JoinModulo u v := by
  obtain ⟨w, haw, hbw⟩ := h
  by_cases hr : rest = .empty
  · subst rest
    exact ⟨w, haw.pre_base ((baseEq_iff_addSummary _ _).mpr (by simpa using hu)),
      hbw.pre_base ((baseEq_iff_addSummary _ _).mpr (by simpa using hv))⟩
  · have hsub : rest.atoms ≤ u.addSummary.atoms := by rw [hu]; exact Multiset.le_add_left _ _
    obtain ⟨tail, htail⟩ := u.add_subsummary_representable rest hsub hr
    exact ⟨.binary .add w tail,
      (haw.context (.binaryLeft .add .hole tail)).pre_base
        ((baseEq_iff_addSummary _ _).mpr (by simpa only [Context.fill, Term.addSummary, htail] using hu)),
      (hbw.context (.binaryLeft .add .hole tail)).pre_base
        ((baseEq_iff_addSummary _ _).mpr (by simpa only [Context.fill, Term.addSummary, htail] using hv))⟩

/-- A single outer addition factor reduces, retaining its full output summary. -/
def AddFactorStep (source target : Term V) : Prop :=
  ∃ a b : Term V, ∃ rest : AddSummary (BaseClass V),
    a.addSummary = (.atom a.baseClass) ∧ ModuloStep a b ∧
    source.addSummary = (AddSummary.atom a.baseClass).combine rest ∧ target.addSummary = b.addSummary.combine rest

theorem AddFactorStep.to_modulo {source target : Term V}
    (h : AddFactorStep source target) : ModuloStep source target := by
  obtain ⟨a, b, rest, ha, hab, hs, ht⟩ := h
  exact hab.of_add_summaries rest (by simpa only [ha] using hs) ht

theorem AddFactorStep.of_base {a b u v : Term V} (h : AddFactorStep a b)
    (hu : BaseEq u a) (hv : BaseEq b v) : AddFactorStep u v := by
  obtain ⟨x, y, rest, hx, hxy, ha, hb⟩ := h
  exact ⟨x, y, rest, hx, hxy, hu.add_summary.trans ha, hv.add_summary.symm.trans hb⟩

theorem AddFactorStep.add_right {a b : Term V} (h : AddFactorStep a b) (t : Term V) :
    AddFactorStep (.binary .add a t) (.binary .add b t) := by
  obtain ⟨x, y, rest, hx, hxy, ha, hb⟩ := h
  exact ⟨x, y, rest.combine t.addSummary, hx, hxy,
    by simp only [Term.addSummary, ha, AddSummary.combine_assoc],
    by simp only [Term.addSummary, hb, AddSummary.combine_assoc]⟩

theorem AddFactorStep.add_left {a b : Term V} (h : AddFactorStep a b) (t : Term V) :
    AddFactorStep (.binary .add t a) (.binary .add t b) :=
  (h.add_right t).of_base (.equation (.comm .add trivial _ _))
    (.equation (.comm .add trivial _ _))

theorem AddFactorStep.of_singleton {a b : Term V} (h : RewriteStep a b)
    (ha : a.addSummary = (.atom a.baseClass)) : AddFactorStep a b :=
  ⟨a, b, .empty, ha, ⟨a, b, .refl _, h, .refl _⟩, by simpa using ha, by simp⟩

/-- There is no addition-root rule. Every raw step reduces one outer factor,
including a multiplication-root fusion that occurs inside that factor. -/
theorem RewriteStep.add_factor {a b : Term V} (h : RewriteStep a b) : AddFactorStep a b := by
  obtain ⟨c, l, r, hr, rfl, rfl⟩ := h
  induction c with
  | hole =>
    cases hr <;> exact AddFactorStep.of_singleton ⟨.hole, _, _, by constructor, rfl, rfl⟩ rfl
  | binaryLeft f c t ih =>
    cases f with
    | add => exact ih.add_right t
    | _ => exact AddFactorStep.of_singleton ⟨_, l, r, hr, rfl, rfl⟩ rfl
  | binaryRight f t c ih =>
    cases f with
    | add => exact ih.add_left t
    | _ => exact AddFactorStep.of_singleton ⟨_, l, r, hr, rfl, rfl⟩ rfl
  | _ => exact AddFactorStep.of_singleton ⟨_, l, r, hr, rfl, rfl⟩ rfl

/-- Arbitrary E0 representatives do not introduce another addition-step case. -/
theorem ModuloStep.add_factor {a b : Term V} (h : ModuloStep a b) : AddFactorStep a b := by
  obtain ⟨x, y, hx, hxy, hy⟩ := h
  exact hxy.add_factor.of_base hx hy

end ExplainableCrypto.Helios.Symbolic
