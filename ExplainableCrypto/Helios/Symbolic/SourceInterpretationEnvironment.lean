import ExplainableCrypto.Helios.Symbolic.SourceInterpretationFrames

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

/-- Changing environment representatives modulo full E preserves all active
constraints and the interpreted body, including under existential locals. -/
theorem Realizes.env_congr {a : Extended V} {env env' : V → Ground} {p : Agent Empty}
    (h : a.Realizes env p) (he : ∀ v, EqE (env v) (env' v)) : a.Realizes env' p := by
  induction a generalizing p with
  | plain a => exact (Agent.EvalEq.of_equivE (a.subst_equivE env env' he).symm).trans h
  | active x m => exact ⟨(he x).symm.trans (h.1.trans (m.subst_congr env env' he)),h.2⟩
  | par a b ha hb =>
    obtain ⟨q,r,hq,hr,hp⟩ := h
    exact ⟨q,r,ha hq he,hb hr he,hp⟩
  | newVar a ih =>
    obtain ⟨m,hm⟩ := h
    refine ⟨m,ih hm ?_⟩
    intro v
    cases v with
    | none => exact .refl _
    | some v => exact he v

theorem realizes_env_congr_iff (a : Extended V) (env env' : V → Ground) (p : Agent Empty)
    (he : ∀ v, EqE (env v) (env' v)) : a.Realizes env p ↔ a.Realizes env' p :=
  ⟨fun h => h.env_congr he,fun h => h.env_congr (fun v => (he v).symm)⟩

theorem shiftTerm_eval (m : Term V) (env : V → Ground) (v : Ground) :
    (shiftTerm m).subst (extendEnv env v) = m.subst env := by
  simp only [shiftTerm,Term.subst_subst,Term.subst,extendEnv]

theorem extendEnv_swapBinders (env : V → Ground) (m n : Ground) :
    (fun v => extendEnv (extendEnv env m) n (swapBinders v)) =
      extendEnv (extendEnv env n) m := by
  funext v
  cases v with
  | none => rfl
  | some v => cases v <;> rfl

theorem Realizes.extend_congr {a : Extended (Option V)} {env : V → Ground}
    {m n : Ground} {p : Agent Empty} (h : a.Realizes (extendEnv env m) p) (he : EqE m n) :
    a.Realizes (extendEnv env n) p := by
  apply h.env_congr
  intro v
  cases v with
  | none => exact he
  | some v => exact .refl _

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
