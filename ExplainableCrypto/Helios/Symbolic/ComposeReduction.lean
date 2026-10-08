import ExplainableCrypto.Helios.Symbolic.ComposeFactors
import ExplainableCrypto.Helios.Symbolic.Confluence

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Lift a specified modulo step through an arbitrary outer composition-factor remainder.
The exact endpoint bags retain multiplicity; empty remainders need no unit. -/
theorem ModuloStep.of_compose_factors {a b u v : Term V} (h : ModuloStep a b)
    (rest : Multiset (BaseClass V))
    (hu : u.composeFactors = a.composeFactors + rest)
    (hv : v.composeFactors = b.composeFactors + rest) : ModuloStep u v := by
  by_cases hr : rest = 0
  · subst rest
    exact (h.pre_base ((baseEq_iff_composeFactors _ _).mpr (by simpa using hu))).post_base
      ((baseEq_iff_composeFactors _ _).mpr (by simpa using hv.symm))
  · have hsub : rest ≤ u.composeFactors := by rw [hu]; exact Multiset.le_add_left _ _
    obtain ⟨tail, htail⟩ := u.compose_subfactors_representable rest hsub hr
    exact ((h.context (.binaryLeft .compose .hole tail)).pre_base
      ((baseEq_iff_composeFactors _ _).mpr (by simpa only [Context.fill, Term.composeFactors, htail] using hu))).post_base
      ((baseEq_iff_composeFactors _ _).mpr (by simpa only [Context.fill, Term.composeFactors, htail] using hv.symm))

/-- Lift a join through arbitrary specified endpoint factor bags. -/
theorem JoinModulo.of_compose_factors {a b u v : Term V} (h : JoinModulo a b)
    (rest : Multiset (BaseClass V))
    (hu : u.composeFactors = a.composeFactors + rest)
    (hv : v.composeFactors = b.composeFactors + rest) : JoinModulo u v := by
  obtain ⟨w, haw, hbw⟩ := h
  by_cases hr : rest = 0
  · subst rest
    exact ⟨w, haw.pre_base ((baseEq_iff_composeFactors _ _).mpr (by simpa using hu)),
      hbw.pre_base ((baseEq_iff_composeFactors _ _).mpr (by simpa using hv))⟩
  · have hsub : rest ≤ u.composeFactors := by rw [hu]; exact Multiset.le_add_left _ _
    obtain ⟨tail, htail⟩ := u.compose_subfactors_representable rest hsub hr
    exact ⟨.binary .compose w tail,
      (haw.context (.binaryLeft .compose .hole tail)).pre_base
        ((baseEq_iff_composeFactors _ _).mpr (by simpa only [Context.fill, Term.composeFactors, htail] using hu)),
      (hbw.context (.binaryLeft .compose .hole tail)).pre_base
        ((baseEq_iff_composeFactors _ _).mpr (by simpa only [Context.fill, Term.composeFactors, htail] using hv))⟩

/-- A single outer composition factor reduces, retaining its full output bag. -/
def ComposeFactorStep (source target : Term V) : Prop :=
  ∃ a b : Term V, ∃ rest : Multiset (BaseClass V),
    a.composeFactors = {a.baseClass} ∧ ModuloStep a b ∧
    source.composeFactors = {a.baseClass} + rest ∧ target.composeFactors = b.composeFactors + rest

theorem ComposeFactorStep.to_modulo {source target : Term V}
    (h : ComposeFactorStep source target) : ModuloStep source target := by
  obtain ⟨a, b, rest, ha, hab, hs, ht⟩ := h
  exact hab.of_compose_factors rest (by simpa only [ha] using hs) ht

theorem ComposeFactorStep.of_base {a b u v : Term V} (h : ComposeFactorStep a b)
    (hu : BaseEq u a) (hv : BaseEq b v) : ComposeFactorStep u v := by
  obtain ⟨x, y, rest, hx, hxy, ha, hb⟩ := h
  exact ⟨x, y, rest, hx, hxy, hu.compose_factors.trans ha, hv.compose_factors.symm.trans hb⟩

theorem ComposeFactorStep.compose_right {a b : Term V} (h : ComposeFactorStep a b) (t : Term V) :
    ComposeFactorStep (.binary .compose a t) (.binary .compose b t) := by
  obtain ⟨x, y, rest, hx, hxy, ha, hb⟩ := h
  exact ⟨x, y, rest + t.composeFactors, hx, hxy,
    by simp only [Term.composeFactors, ha, Multiset.add_assoc],
    by simp only [Term.composeFactors, hb, Multiset.add_assoc]⟩

theorem ComposeFactorStep.compose_left {a b : Term V} (h : ComposeFactorStep a b) (t : Term V) :
    ComposeFactorStep (.binary .compose t a) (.binary .compose t b) :=
  (h.compose_right t).of_base (.equation (.comm .compose trivial _ _))
    (.equation (.comm .compose trivial _ _))

theorem ComposeFactorStep.of_singleton {a b : Term V} (h : RewriteStep a b)
    (ha : a.composeFactors = {a.baseClass}) : ComposeFactorStep a b :=
  ⟨a, b, 0, ha, ⟨a, b, .refl _, h, .refl _⟩, by simpa using ha, by simp⟩

/-- There is no composition-root rule. Every raw step reduces one outer factor,
including a multiplication-root fusion that occurs inside that factor. -/
theorem RewriteStep.compose_factor {a b : Term V} (h : RewriteStep a b) : ComposeFactorStep a b := by
  obtain ⟨c, l, r, hr, rfl, rfl⟩ := h
  induction c with
  | hole =>
    cases hr <;> exact ComposeFactorStep.of_singleton ⟨.hole, _, _, by constructor, rfl, rfl⟩ rfl
  | binaryLeft f c t ih =>
    cases f with
    | compose => exact ih.compose_right t
    | _ => exact ComposeFactorStep.of_singleton ⟨_, l, r, hr, rfl, rfl⟩ rfl
  | binaryRight f t c ih =>
    cases f with
    | compose => exact ih.compose_left t
    | _ => exact ComposeFactorStep.of_singleton ⟨_, l, r, hr, rfl, rfl⟩ rfl
  | _ => exact ComposeFactorStep.of_singleton ⟨_, l, r, hr, rfl, rfl⟩ rfl

/-- Arbitrary E0 representatives do not introduce another composition-step case. -/
theorem ModuloStep.compose_factor {a b : Term V} (h : ModuloStep a b) : ComposeFactorStep a b := by
  obtain ⟨x, y, hx, hxy, hy⟩ := h
  exact hxy.compose_factor.of_base hx hy

end ExplainableCrypto.Helios.Symbolic
