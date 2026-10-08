import ExplainableCrypto.Helios.Symbolic.CiphertextObservationInduction

namespace ExplainableCrypto.Helios.Symbolic

/-- An equally small public equivalent of a minimum is itself minimum. -/
theorem MinimalRecipe.of_equivalent_size {V W : Type} {restricted : Finset Nat}
    {σ : V → Term W} {r m : Term V} (hm : MinimalRecipe restricted σ m)
    (hr : r.Public restricted) (he : EqE (r.subst σ) (m.subst σ))
    (hsize : r.nodeCount ≤ m.nodeCount) : MinimalRecipe restricted σ r := by
  refine ⟨hr, fun s hs hes => ?_⟩
  exact hsize.trans (hm.least s hs (he.symm.trans hes))

namespace Frame
variable {restricted : Finset Nat} {n : Nat} {φ ψ : Frame restricted n}

/-- The same source-minimum representative must preserve evaluation in both worlds. -/
def SharedMinimum (φ ψ : Frame restricted n) (r : Recipe n) : Prop :=
  ∃ m, MinimalRecipe restricted φ.value m ∧
    EqE (φ.eval r) (φ.eval m) ∧ EqE (ψ.eval r) (ψ.eval m)

def CommonMinima (φ ψ : Frame restricted n) : Prop :=
  ∀ r, r.Public restricted → SharedMinimum φ ψ r

/-- This packages a still-required branch assembly; it does not assert it for Helios. -/
def MinimumObservationStep (φ ψ : Frame restricted n) : Prop :=
  ∀ r s, MinimalRecipe restricted φ.value r → MinimalRecipe restricted φ.value s →
    ObservationsBelow φ ψ (r.nodeCount + s.nodeCount) →
    (EqE (φ.eval r) (φ.eval s) ↔ EqE (ψ.eval r) (ψ.eval s))

theorem SharedMinimum.of_minimal {r : Recipe n}
    (hr : MinimalRecipe restricted φ.value r) : SharedMinimum φ ψ r :=
  ⟨r, hr, .refl _, .refl _⟩

/-- Pre-substitution E equality transports through every destination frame. -/
theorem SharedMinimum.of_recipe_eqE {r m : Recipe n}
    (hm : MinimalRecipe restricted φ.value m) (he : EqE r m) : SharedMinimum φ ψ r :=
  ⟨m, hm, he.subst φ.value, he.subst ψ.value⟩

theorem SharedMinimum.of_raw_reduces {r m : Recipe n}
    (hm : MinimalRecipe restricted φ.value m) (h : RawReduces r m) :
    SharedMinimum φ ψ r :=
  .of_recipe_eqE hm h.to_modulo.sound

/-- Ordinary normalization suffices when its result actually attains the minimum.
Raw normality alone is not this premise. -/
theorem SharedMinimum.of_raw_normalization (r : Recipe n)
    (hm : MinimalRecipe restricted φ.value (normalizeRaw r)) : SharedMinimum φ ψ r :=
  .of_raw_reduces hm (normalizeRaw_reachable r)

/-- A necessary condition, useful for auditing transport assumptions, not proving them. -/
theorem StaticEq.common_minima (h : StaticEq φ ψ) : CommonMinima φ ψ := by
  intro r hr
  obtain ⟨m, hm, he⟩ := exists_minimal_recipe (σ := φ.value) r hr
  exact ⟨m, hm, he, (h r m hr hm.isPublic).1 he⟩

/-- Strong total-size induction closes the gap only with explicit shared transport. -/
theorem staticEq_of_common_minima (hcommon : CommonMinima φ ψ)
    (hstep : MinimumObservationStep φ ψ) : StaticEq φ ψ := by
  have induction : ∀ k, ∀ r s : Recipe n, r.Public restricted → s.Public restricted →
      r.nodeCount + s.nodeCount = k →
      (EqE (φ.eval r) (φ.eval s) ↔ EqE (ψ.eval r) (ψ.eval s)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro r s hr hs hk
      obtain ⟨a, ha, hra, hra'⟩ := hcommon r hr
      obtain ⟨b, hb, hsb, hsb'⟩ := hcommon s hs
      have hleA := ha.least r hr hra.symm
      have hleB := hb.least s hs hsb.symm
      by_cases hlt : a.nodeCount + b.nodeCount < k
      · have hab := ih _ hlt a b ha.isPublic hb.isPublic rfl
        exact ⟨fun he => hra'.trans ((hab.1 (hra.symm.trans (he.trans hsb))).trans hsb'.symm),
          fun he => hra.trans ((hab.2 (hra'.symm.trans (he.trans hsb'))).trans hsb.symm)⟩
      · have hmr := ha.of_equivalent_size hr hra (by omega)
        have hms := hb.of_equivalent_size hs hsb (by omega)
        apply hstep r s hmr hms
        intro a b ha hb hsize
        exact ih _ (by omega) a b ha hb rfl
  intro r s hr hs
  exact induction _ r s hr hs rfl

/-- Reverse shared minimization carries a source minimum into the destination. -/
theorem CommonMinima.minimum_destination (h : CommonMinima ψ φ) {r : Recipe n}
    (hr : MinimalRecipe restricted φ.value r) : MinimalRecipe restricted ψ.value r := by
  obtain ⟨m, hm, he, he'⟩ := h r hr.isPublic
  exact hm.of_equivalent_size hr.isPublic he (hr.least m hm.isPublic he')

end Frame
end ExplainableCrypto.Helios.Symbolic
