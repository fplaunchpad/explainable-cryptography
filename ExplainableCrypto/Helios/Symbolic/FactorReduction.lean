import ExplainableCrypto.Helios.Symbolic.FactorReconstruction
import ExplainableCrypto.Helios.Symbolic.Confluence

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Lift a specified modulo step through an arbitrary outer factor remainder.
The exact endpoint bags retain multiplicity; empty remainders need no unit. -/
theorem ModuloStep.of_factors {a b u v : Term V} (h : ModuloStep a b)
    (rest : Multiset (BaseClass V))
    (hu : u.mulFactors = a.mulFactors + rest)
    (hv : v.mulFactors = b.mulFactors + rest) : ModuloStep u v := by
  by_cases hr : rest = 0
  · subst rest
    exact (h.pre_base ((baseEq_iff_mulFactors _ _).mpr (by simpa using hu))).post_base
      ((baseEq_iff_mulFactors _ _).mpr (by simpa using hv.symm))
  · have hsub : rest ≤ u.mulFactors := by rw [hu]; exact Multiset.le_add_left _ _
    obtain ⟨tail, htail⟩ := u.subfactors_representable rest hsub hr
    exact ((h.context (.binaryLeft .mul .hole tail)).pre_base
      ((baseEq_iff_mulFactors _ _).mpr (by simpa only [Context.fill, Term.mulFactors, htail] using hu))).post_base
      ((baseEq_iff_mulFactors _ _).mpr (by simpa only [Context.fill, Term.mulFactors, htail] using hv.symm))

/-- Lift a join through arbitrary specified endpoint factor bags. -/
theorem JoinModulo.of_factors {a b u v : Term V} (h : JoinModulo a b)
    (rest : Multiset (BaseClass V))
    (hu : u.mulFactors = a.mulFactors + rest)
    (hv : v.mulFactors = b.mulFactors + rest) : JoinModulo u v := by
  obtain ⟨w, haw, hbw⟩ := h
  by_cases hr : rest = 0
  · subst rest
    exact ⟨w, haw.pre_base ((baseEq_iff_mulFactors _ _).mpr (by simpa using hu)),
      hbw.pre_base ((baseEq_iff_mulFactors _ _).mpr (by simpa using hv))⟩
  · have hsub : rest ≤ u.mulFactors := by rw [hu]; exact Multiset.le_add_left _ _
    obtain ⟨tail, htail⟩ := u.subfactors_representable rest hsub hr
    exact ⟨.binary .mul w tail,
      (haw.context (.binaryLeft .mul .hole tail)).pre_base
        ((baseEq_iff_mulFactors _ _).mpr (by simpa only [Context.fill, Term.mulFactors, htail] using hu)),
      (hbw.context (.binaryLeft .mul .hole tail)).pre_base
        ((baseEq_iff_mulFactors _ _).mpr (by simpa only [Context.fill, Term.mulFactors, htail] using hv))⟩

end ExplainableCrypto.Helios.Symbolic
