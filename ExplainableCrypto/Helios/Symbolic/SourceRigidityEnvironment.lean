import ExplainableCrypto.Helios.Symbolic.SourceRigidityPreservation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

/-- Active constraints depend only on the full-E classes of environment values. -/
theorem satisfies_env_congr (a : Extended V) (env env' : V → Ground)
    (he : ∀ v, EqE (env v) (env' v)) : a.Satisfies env ↔ a.Satisfies env' := by
  rw [satisfies_iff_realizes,satisfies_iff_realizes]
  exact realizes_env_congr_iff a.frameOf env env' .nil he

/-- Local uniqueness is independent of the choice of E-equivalent outer
representatives, including beneath further restricted variables. -/
theorem rigid_env_congr (a : Extended V) (env env' : V → Ground)
    (he : ∀ v, EqE (env v) (env' v)) : a.Rigid env ↔ a.Rigid env' := by
  induction a with
  | plain | active => rfl
  | par a b ha hb => simp only [Rigid,satisfies_env_congr a env env' he,
      satisfies_env_congr b env env' he,ha env env' he,hb env env' he]
  | newVar a ih =>
    have hex (m : Ground) : ∀ v, EqE (extendEnv env m v) (extendEnv env' m v) := by
      intro v
      cases v with
      | none => exact .refl _
      | some v => exact he v
    simp only [Rigid,satisfies_env_congr a _ _ (hex _),ih _ _ (hex _)]

/-- A rigid restriction has a rigid body at any chosen value; inconsistent
choices are handled by the same vacuity rule, not by an existence assumption. -/
theorem rigid_newVar_body {a : Extended (Option V)} {env : V → Ground}
    (h : (Extended.newVar a).Rigid env) (m : Ground) : a.Rigid (extendEnv env m) := by
  by_cases hm : a.Satisfies (extendEnv env m)
  · exact h.2 m hm
  · exact rigid_of_not_satisfies a _ hm

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
