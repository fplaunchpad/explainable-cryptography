import ExplainableCrypto.Helios.Symbolic.ConstructedCompression

namespace ExplainableCrypto.Helios.Symbolic.Frame
variable {restricted : Finset Nat} {n : Nat} {φ ψ : Frame restricted n}

/-- The bound applies to each original recipe, not to its comparison with
the chosen minimum. It is the strict induction frontier. -/
def SharedMinimaBelow (φ ψ : Frame restricted n) (bound : Nat) : Prop :=
  ∀ r, r.Public restricted → r.nodeCount < bound → SharedMinimum φ ψ r

theorem SharedMinimaBelow.mono {a b : Nat} (h : SharedMinimaBelow φ ψ b) (hle : a ≤ b) :
    SharedMinimaBelow φ ψ a :=
  fun r hp hr => h r hp (Nat.lt_of_lt_of_le hr hle)

/-- Only this recipe's reverse shared minimum is needed to transfer its
minimum status. No universal frame-equivalence premise is used. -/
theorem SharedMinimum.minimum_destination {r : Recipe n} (h : SharedMinimum ψ φ r)
    (hr : MinimalRecipe restricted φ.value r) : MinimalRecipe restricted ψ.value r := by
  obtain ⟨m,hm,he,he'⟩ := h
  exact hm.of_equivalent_size hr.isPublic he (hr.least m hm.isPublic he')

/-- Total-test-size induction stays below the supplied recipe bound. Both
transport directions and the both-minimum observation step are indispensable. -/
theorem observationsBelow_of_shared_minima {bound : Nat}
    (hforward : SharedMinimaBelow φ ψ bound) (hreverse : SharedMinimaBelow ψ φ bound)
    (hstep : ∀ r s, MinimalRecipe restricted φ.value r → MinimalRecipe restricted φ.value s →
      MinimalRecipe restricted ψ.value r → MinimalRecipe restricted ψ.value s →
      ObservationsBelow φ ψ (r.nodeCount+s.nodeCount) →
      (EqE (φ.eval r) (φ.eval s) ↔ EqE (ψ.eval r) (ψ.eval s))) :
    ObservationsBelow φ ψ bound := by
  have induction : ∀ k, k < bound → ∀ r s : Recipe n,
      r.Public restricted → s.Public restricted → r.nodeCount+s.nodeCount=k →
      (EqE (φ.eval r) (φ.eval s) ↔ EqE (ψ.eval r) (ψ.eval s)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk r s hr hs hsize
      have hrb : r.nodeCount < bound := by omega
      have hsb : s.nodeCount < bound := by omega
      obtain ⟨a,ha,hra,hra'⟩ := hforward r hr hrb
      obtain ⟨b,hb,hsbEq,hsbEq'⟩ := hforward s hs hsb
      have hla := ha.least r hr hra.symm
      have hlb := hb.least s hs hsbEq.symm
      by_cases hlt : a.nodeCount+b.nodeCount < k
      · have he := ih _ hlt (by omega) a b ha.isPublic hb.isPublic rfl
        exact ⟨fun h => hra'.trans ((he.mp (hra.symm.trans (h.trans hsbEq))).trans hsbEq'.symm),
          fun h => hra.trans ((he.mpr (hra'.symm.trans (h.trans hsbEq'))).trans hsbEq.symm)⟩
      · have hmr := ha.of_equivalent_size hr hra (by omega)
        have hms := hb.of_equivalent_size hs hsbEq (by omega)
        apply hstep r s hmr hms ((hreverse r hr hrb).minimum_destination hmr)
          ((hreverse s hs hsb).minimum_destination hms)
        intro u v hu hv hlt
        exact ih _ (by omega) (by omega) u v hu hv rfl
  intro r s hr hs hb
  exact induction _ hb r s hr hs rfl

end ExplainableCrypto.Helios.Symbolic.Frame

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- The checked historical minimum-observation assembly supplies the step;
two-way shared minima below the same bound supply all its remaining premises. -/
theorem observationsBelow_of_two_way_minima (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (bound : Nat)
    (hforward : Frame.SharedMinimaBelow (frame ns swap left right) (frame ns swap' left right) bound)
    (hreverse : Frame.SharedMinimaBelow (frame ns swap' left right) (frame ns swap left right) bound) :
    Frame.ObservationsBelow (frame ns swap left right) (frame ns swap' left right) bound := by
  cases swap <;> cases swap'
  · intro r s _ _ _; exact Iff.rfl
  · exact Frame.observationsBelow_of_shared_minima hforward hreverse
      (minimum_equality_swap_of_both_minima ns hf left right)
  · exact Frame.observationsBelow_of_shared_minima hforward hreverse
      (minimum_equality_swap_of_both_minima ns hf right left)
  · intro r s _ _ _; exact Iff.rfl

/-- Constructed-only compression needs only the two strict smaller-minimum
hypotheses that a simultaneous recipe-size induction provides. -/
theorem constructed_mul_shared_of_two_way_minima (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (a b : CiphertextAssembly n)
    (hp : (a.mul b).recipe.Public ns.restricted) {r p : Recipe 3}
    (hg : (a.mul b).group = .constructed r p) (hc : (a.mul b).Coherent (frame ns swap left right))
    (hforward : Frame.SharedMinimaBelow (frame ns swap left right) (frame ns swap' left right) (a.mul b).recipe.nodeCount)
    (hreverse : Frame.SharedMinimaBelow (frame ns swap' left right) (frame ns swap left right) (a.mul b).recipe.nodeCount) :
    Frame.SharedMinimum (frame ns swap left right) (frame ns swap' left right) (a.mul b).recipe :=
  constructed_mul_shared_of_smaller_observations ns swap swap' left right a b hp hg hc
    (observationsBelow_of_two_way_minima ns hf swap swap' left right _ hforward hreverse) hforward

end ExplainableCrypto.Helios.Symbolic.Historical.General
