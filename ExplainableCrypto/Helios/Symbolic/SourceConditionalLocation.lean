import ExplainableCrypto.Helios.Symbolic.SourceConditionalReadiness

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V : Type}

namespace Extended

theorem InternalStep.conditional_realizes_ready {kind : InternalKind} {a b : Extended V}
    (h : InternalStep kind a b) (taken : Bool) (hk : kind = .conditional taken)
    (f g : Nat → Nat) (env : V → Ground) {p : Agent Empty}
    (ha : (a.mapNames f g).Realizes env p) : p.HasConditional := by
  induction h generalizing p with
  | atomComm => cases hk
  | thenBranch => exact ha.hasConditional.mp trivial
  | elseBranch => exact ha.hasConditional.mp trivial
  | parLeft c h ih =>
    obtain ⟨r,s,hr,hs,he⟩ := ha
    exact he.hasConditional.mp (.inl (ih hk env hr))
  | parRight c h ih =>
    obtain ⟨r,s,hr,hs,he⟩ := ha
    exact he.hasConditional.mp (.inr (ih hk env hs))
  | newVar h ih =>
    obtain ⟨m,hm⟩ := ha
    exact ih hk (extendEnv env m) hm
  | congr hs h ht ih =>
    exact ih hk env (((hs.mapNames f g).realizes env p).mp ha)

end Extended

namespace Named

theorem InternalStep.conditional_interprets_ready {kind : InternalKind} {a b : Named V}
    (h : InternalStep kind a b) (taken : Bool) (hk : kind = .conditional taken)
    (ρ : NameAssignment) (env : V → Ground) {p : Agent Empty}
    (ha : a.Interprets ρ env p) : p.HasConditional := by
  induction h generalizing ρ p with
  | embed h => exact h.conditional_realizes_ready taken hk ρ.base ρ.channel env ha
  | parLeft c h ih =>
    obtain ⟨r,s,hr,hs,he⟩ := ha
    exact he.hasConditional.mp (.inl (ih hk ρ env hr))
  | parRight c h ih =>
    obtain ⟨r,s,hr,hs,he⟩ := ha
    exact he.hasConditional.mp (.inr (ih hk ρ env hs))
  | newName n h ih =>
    obtain ⟨v,hv⟩ := ha
    exact ih hk (Function.update ρ n v) env hv
  | newVar h ih =>
    obtain ⟨m,hm⟩ := ha
    exact ih hk ρ (extendEnv env m) hm
  | congr hs h ht ih => exact ih hk ρ env ((hs.interprets ρ env p).mp ha)

/-- When no conditional is ready, an arbitrary original reduction is an actual
classified communication. There is no communication premise here. -/
theorem Reduction.communication_of_no_conditional {a b : Named V}
    (h : Reduction a b) (ρ : NameAssignment) (env : V → Ground) {p : Agent Empty}
    (ha : a.Interprets ρ env p) (hn : ¬ p.HasConditional) :
    InternalStep .communication a b := by
  obtain ⟨kind,hk⟩ := h.classify
  cases kind with
  | communication => exact hk
  | conditional taken => exact (hn (hk.conditional_interprets_ready taken rfl ρ env ha)).elim

theorem Reduction.interprets_of_no_conditional {a b : Named V}
    (h : Reduction a b) (ρ : NameAssignment) (env : V → Ground) {p : Agent Empty}
    (ha : a.Interprets ρ env p) (hn : ¬ p.HasConditional) :
    ∃ q, Agent.Tau p q ∧ b.Interprets ρ env q :=
  (h.communication_of_no_conditional ρ env ha hn).communication_interprets ρ env ha

end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
