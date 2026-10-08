import ExplainableCrypto.Helios.Symbolic.SourceInterpretationVisibleFrames

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

theorem active_plain_realizes_iff (x : V) (m : Term V) (a : Agent V)
    (env : V → Ground) (p : Agent Empty) :
    (par (.active x m) (.plain a)).Realizes env p ↔
      EqE (env x) (m.subst env) ∧ Agent.EvalEq (a.subst env) p := by
  have hn : Agent.ParEq (.par .nil (a.subst env)) (a.subst env) :=
    (Agent.ParEq.comm _ _).trans (.zero _)
  constructor
  · rintro ⟨q,r,⟨hm,hq⟩,hr,hp⟩
    exact ⟨hm,(Agent.EvalEq.of_parEq hn.symm).trans ((Agent.EvalEq.par hq hr).trans hp)⟩
  · rintro ⟨hm,hp⟩
    exact ⟨.nil,a.subst env,⟨hm,.refl _⟩,.refl _,(Agent.EvalEq.of_parEq hn).trans hp⟩

/-- Capturing a payload imposes its complete E-value at the new binder and
evaluates the old continuation under the unchanged old environment. -/
theorem capture_realizes_iff (m : Term V) (a : Agent V) (env : V → Ground)
    (n : Ground) (p : Agent Empty) : (capture m a).Realizes (extendEnv env n) p ↔
      EqE n (m.subst env) ∧ Agent.EvalEq (a.subst env) p := by
  rw [capture,active_plain_realizes_iff,shiftTerm_eval]
  simp only [Agent.shift,Agent.subst_subst,Term.subst,extendEnv]

theorem capture_ground_realizes_iff (m : Ground) (a : Agent Empty) (env : V → Ground)
    (n : Ground) (p : Agent Empty) :
    (capture (groundTerm m) (groundAgent a)).Realizes (extendEnv env n) p ↔
      EqE n m ∧ Agent.EvalEq a p := by
  rw [capture_realizes_iff,groundTerm_eval,groundAgent_eval]

/-- No promise of a unique syntactic representative is needed: every
E-equivalent complete message is a valid environment representative. -/
theorem capture_realizes (m : Term V) (a : Agent V) (env : V → Ground)
    {n : Ground} (hn : EqE n (m.subst env)) :
    (capture m a).Realizes (extendEnv env n) (a.subst env) :=
  (capture_realizes_iff m a env n (a.subst env)).mpr ⟨hn,.refl _⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
