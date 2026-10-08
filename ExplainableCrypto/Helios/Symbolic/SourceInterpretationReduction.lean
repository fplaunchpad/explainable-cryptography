import ExplainableCrypto.Helios.Symbolic.SourceInterpretationStructure

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

/-- Every current extended internal reduction has a genuine interpreted Tau,
including arbitrary structural paths and existential variable restrictions. -/
theorem Reduction.realizes {a b : Extended V} (h : Reduction a b)
    (env : V → Ground) {p : Agent Empty} (ha : a.Realizes env p) :
    ∃ q, Agent.Tau p q ∧ b.Realizes env q := by
  induction h generalizing p with
  | atomComm c x a b =>
    have hc : Agent.Tau ((Agent.par (.output c (.var x) a) (.input c b)).subst env)
        ((Agent.par a (b.bind (.var x))).subst env) := by
      have hb := Agent.bind_subst b (.var x) env
      change (b.subst (liftSubst env)).bind (env x) = (b.bind (.var x)).subst env at hb
      simpa only [Agent.subst,Term.subst,← hb] using
        Agent.Tau.of_core (Agent.CoreStep.comm c (env x) (a.subst env) (b.subst (liftSubst env)))
    obtain ⟨q,hq,he⟩ := ha.tau_transport hc
    exact ⟨q,hq,he⟩
  | thenBranch f a b hf =>
    have hg : ((f.subst Empty.elim).subst env).Holds Empty.elim := by
      rw [Formula.holds_subst,Formula.holds_subst]
      have he : (fun v : Empty => (Empty.elim v : Term _).subst (fun w => (env w).subst Empty.elim)) =
          (Empty.elim : Empty → Ground) := by funext v; exact v.elim
      rw [he]
      exact hf
    obtain ⟨q,hq,he⟩ := ha.tau_transport (Agent.Tau.of_core (Agent.CoreStep.thenBranch _ _ _ hg))
    exact ⟨q,hq,he⟩
  | elseBranch f a b hf =>
    have hg : ¬ ((f.subst Empty.elim).subst env).Holds Empty.elim := by
      rw [Formula.holds_subst,Formula.holds_subst]
      have he : (fun v : Empty => (Empty.elim v : Term _).subst (fun w => (env w).subst Empty.elim)) =
          (Empty.elim : Empty → Ground) := by funext v; exact v.elim
      rw [he]
      exact hf
    obtain ⟨q,hq,he⟩ := ha.tau_transport (Agent.Tau.of_core (Agent.CoreStep.elseBranch _ _ _ hg))
    exact ⟨q,hq,he⟩
  | parLeft c h ih =>
    obtain ⟨r,s,hr,hs,he⟩ := ha
    obtain ⟨r',ht,hr'⟩ := ih env hr
    obtain ⟨q,hq,he'⟩ := he.tau_transport (ht.parLeft s)
    exact ⟨q,hq,(realizes_par _ _ _ hr' hs).congr he'⟩
  | parRight c h ih =>
    obtain ⟨r,s,hr,hs,he⟩ := ha
    obtain ⟨s',ht,hs'⟩ := ih env hs
    obtain ⟨q,hq,he'⟩ := he.tau_transport (ht.parRight r)
    exact ⟨q,hq,(realizes_par _ _ _ hr hs').congr he'⟩
  | newVar h ih =>
    obtain ⟨m,hm⟩ := ha
    obtain ⟨q,hq,he⟩ := ih (extendEnv env m) hm
    exact ⟨q,hq,m,he⟩
  | congr hs h ht ih =>
    obtain ⟨q,hq,he⟩ := ih env ((hs.realizes env p).mp ha)
    exact ⟨q,hq,(ht.realizes env q).mp he⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
