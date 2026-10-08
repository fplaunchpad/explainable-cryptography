import ExplainableCrypto.Helios.Symbolic.SourceIndependentFrameCompatibility

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type} {a b : Named V}

theorem Reduction.models (h : Reduction a b) (ρ : Nat → Nat) (env : V → Ground) :
    a.Models ρ env ↔ b.Models ρ env :=
  (models_frameOf a ρ env).symm.trans ((h.frameOf.models ρ env).trans (models_frameOf b ρ env))

theorem FreeStep.models {l : Extended.FreeLabel V} (h : FreeStep a l b)
    (ρ : Nat → Nat) (env : V → Ground) : a.Models ρ env ↔ b.Models ρ env :=
  (models_frameOf a ρ env).symm.trans ((h.frameOf.models ρ env).trans (models_frameOf b ρ env))

theorem BoundOutput.models_reclose {b : Named (Option V)} {c : Nat} (h : BoundOutput a c b)
    (ρ : Nat → Nat) (env : V → Ground) : (newVar b).Models ρ env ↔ a.Models ρ env :=
  (models_frameOf (newVar b) ρ env).symm.trans
    ((h.frameOf_reclose.models ρ env).trans (models_frameOf a ρ env))

theorem Reduction.validEquation_iff (h : Reduction a b) (r s : Term V) :
    a.ValidEquation r s ↔ b.ValidEquation r s := by
  simp only [ValidEquation,h.models]

theorem FreeStep.validEquation_iff {l : Extended.FreeLabel V} (h : FreeStep a l b) (r s : Term V) :
    a.ValidEquation r s ↔ b.ValidEquation r s := by
  simp only [ValidEquation,h.models]

/-- Hiding one variable is exactly quantification over its full ground value.
Old terms are shifted when tested in the larger variable domain. -/
theorem validEquation_newVar_iff (b : Named (Option V)) (r s : Term V) :
    (newVar b).ValidEquation r s ↔ b.ValidEquation (shiftTerm r) (shiftTerm s) := by
  constructor
  · intro h env hm
    have he : extendEnv (fun v => env (some v)) (env none) = env := by funext v; cases v <;> rfl
    have hx := h (fun v => env (some v)) ⟨env none,by simpa only [he] using hm⟩
    simpa only [shiftTerm,Term.subst_subst,Term.subst] using hx
  · intro h env hm
    obtain ⟨m,hm⟩ := hm
    simpa only [Extended.shiftTerm_eval] using h (extendEnv env m) hm

/-- A bound publication keeps every equation over old exported variables,
while allowing additional observations involving its genuinely new handle. -/
theorem BoundOutput.old_validEquation_iff {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) (r s : Term V) :
    a.ValidEquation r s ↔ b.ValidEquation (shiftTerm r) (shiftTerm s) := by
  have hr : a.ValidEquation r s ↔ (newVar b).ValidEquation r s := by
    simp only [ValidEquation,h.models_reclose]
  exact hr.trans (validEquation_newVar_iff b r s)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
