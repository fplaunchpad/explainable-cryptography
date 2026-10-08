import ExplainableCrypto.Helios.Symbolic.SourceInterpretedLabels

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

/-- Every current free source action has interpreted visible behavior, through
variable Scope, parallel contexts and arbitrary active structural paths. -/
theorem FreeStep.realizes {a b : Extended V} {l : FreeLabel V} (h : FreeStep a l b)
    (env : V → Ground) {p : Agent Empty} (ha : a.Realizes env p) :
    ∃ q, l.RealizedStep env p q ∧ b.Realizes env q := by
  induction h generalizing p with
  | input c m body =>
    have hc : Agent.Visible ((Agent.input c body).subst env) (.input c (m.subst env))
        ((body.bind m).subst env) := by
      simpa only [Agent.subst,Agent.bind_subst] using
        Agent.Visible.of_core (Agent.CoreVisible.input c (m.subst env) (body.subst (liftSubst env)))
    obtain ⟨q,hq,he⟩ := ha.input_transport hc (.refl _)
    exact ⟨q,hq,he⟩
  | output c x body =>
    have hc : (FreeLabel.output c x).RealizedStep env
        ((Agent.output c (.var x) body).subst env) (body.subst env) :=
      ⟨env x,.refl _,.of_core (.output _ _ _)⟩
    obtain ⟨q,hq,he⟩ := hc.transport ha
    exact ⟨q,hq,he⟩
  | scopeInput h ih =>
    obtain ⟨v,hv⟩ := ha
    obtain ⟨q,hq,he⟩ := ih (extendEnv env v) hv
    exact ⟨q,by simpa only [FreeLabel.RealizedStep,shiftTerm_eval] using hq,⟨v,he⟩⟩
  | scopeOutput h ih =>
    obtain ⟨v,hv⟩ := ha
    obtain ⟨q,hq,he⟩ := ih (extendEnv env v) hv
    exact ⟨q,hq,⟨v,he⟩⟩
  | parLeft c h ih =>
    obtain ⟨r,s,hr,hs,he⟩ := ha
    obtain ⟨r',ht,hr'⟩ := ih env hr
    obtain ⟨q,hq,he'⟩ := (ht.parLeft s).transport he
    exact ⟨q,hq,(realizes_par _ _ _ hr' hs).congr he'⟩
  | parRight c h ih =>
    obtain ⟨r,s,hr,hs,he⟩ := ha
    obtain ⟨s',ht,hs'⟩ := ih env hs
    obtain ⟨q,hq,he'⟩ := (ht.parRight r).transport he
    exact ⟨q,hq,(realizes_par _ _ _ hr hs').congr he'⟩
  | congr hs h ht ih =>
    obtain ⟨q,hq,he⟩ := ih env ((hs.realizes env p).mp ha)
    exact ⟨q,hq,(ht.realizes env q).mp he⟩

theorem FreeStep.input_realizes {a b : Extended V} {c : Nat} {m : Term V}
    (h : FreeStep a (.input c m) b) (env : V → Ground) {p : Agent Empty}
    (ha : a.Realizes env p) :
    ∃ q, Agent.Visible p (.input c (m.subst env)) q ∧ b.Realizes env q := h.realizes env ha

theorem FreeStep.output_realizes {a b : Extended V} {c : Nat} {x : V}
    (h : FreeStep a (.output c x) b) (env : V → Ground) {p : Agent Empty}
    (ha : a.Realizes env p) :
    ∃ m q, EqE (env x) m ∧ Agent.Visible p (.output c m) q ∧ b.Realizes env q := by
  obtain ⟨q,⟨m,hm,hq⟩,he⟩ := h.realizes env ha
  exact ⟨m,q,hm,hq,he⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
