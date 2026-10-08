import ExplainableCrypto.Helios.Symbolic.SourceRigidityEnvironment

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

private theorem rigid_swapped_locals (a : Extended (Option (Option V))) (env : V → Ground)
    (h : (Extended.newVar (.newVar a)).Rigid env) :
    (Extended.newVar (.newVar (a.rename swapBinders))).Rigid env := by
  simp only [Rigid,Satisfies,satisfies_rename,rigid_rename,extendEnv_swapBinders] at h ⊢
  have outer (m n v : Ground) (he : EqE m n) :
      a.Satisfies (extendEnv (extendEnv env m) v) ↔
        a.Satisfies (extendEnv (extendEnv env n) v) := by
    apply satisfies_env_congr
    intro x
    cases x with
    | none => exact .refl _
    | some x => cases x with
      | none => exact he
      | some x => exact .refl _
  constructor
  · intro m n ⟨v,hv⟩ ⟨w,hw⟩
    have hvw := h.1 v w ⟨m,hv⟩ ⟨n,hw⟩
    exact (h.2 v ⟨m,hv⟩).1 m n hv ((outer v w n hvw).mpr hw)
  · intro m ⟨v,hv⟩
    constructor
    · intro v w hv hw
      exact h.1 v w ⟨m,hv⟩ ⟨m,hw⟩
    · intro w hw
      exact (h.2 w ⟨m,hw⟩).2 m hw

/-- Source variable commutation changes coordinates of the two local values.
Their uniqueness is modulo E, so transporting the other value's constraints
across an E-equivalent environment is essential. -/
theorem rigid_varComm (a : Extended (Option (Option V))) (env : V → Ground) :
    (Extended.newVar (.newVar a)).Rigid env ↔
      (Extended.newVar (.newVar (a.rename swapBinders))).Rigid env := by
  constructor
  · exact rigid_swapped_locals a env
  · intro h
    have hh := rigid_swapped_locals (a.rename swapBinders) env h
    have hs : (a.rename swapBinders).rename swapBinders = a := by
      rw [rename_comp]
      have he : (swapBinders ∘ swapBinders : Option (Option V) → Option (Option V)) = id := by
        funext v
        cases v with
        | none => rfl
        | some v => cases v <;> rfl
      rw [he,rename_id]
    rwa [hs] at hh

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
