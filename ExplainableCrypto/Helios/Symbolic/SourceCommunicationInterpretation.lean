import ExplainableCrypto.Helios.Symbolic.SourceClassifiedInternal

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V : Type} {restricted hidden : Finset Nat} {handles : Nat}

namespace Extended

/-- Forward communication uses no equality reflection. Both endpoints of its
channel remain equal under every map, even when other channels collide. -/
theorem InternalStep.mapNames_of_communication {kind : InternalKind} {a b : Extended V}
    (h : InternalStep kind a b) (hk : kind = .communication) (f g : Nat → Nat) :
    InternalStep .communication (a.mapNames f g) (b.mapNames f g) := by
  induction h with
  | atomComm c x p q =>
    simpa only [Extended.mapNames,Agent.mapNames,Agent.mapNames_bind,Term.mapNames] using
      InternalStep.atomComm (g c) x (p.mapNames f g) (q.mapNames f g)
  | thenBranch => cases hk
  | elseBranch => cases hk
  | parLeft c h ih => exact .parLeft _ (ih hk)
  | parRight a h ih => exact .parRight _ (ih hk)
  | newVar h ih => exact .newVar (ih hk)
  | congr hs h ht ih => exact .congr (hs.mapNames f g) (ih hk) (ht.mapNames f g)

theorem InternalStep.communication_realizes {a b : Extended V}
    (h : InternalStep .communication a b) (ρ : NameAssignment) (env : V → Ground)
    {p : Agent Empty} (ha : (a.mapNames ρ.base ρ.channel).Realizes env p) :
    ∃ q, Agent.Tau p q ∧ (b.mapNames ρ.base ρ.channel).Realizes env q :=
  (h.mapNames_of_communication rfl ρ.base ρ.channel).reduction.realizes env ha

end Extended

namespace Named

/-- Arbitrary name restrictions, alpha, active substitutions and variable
contexts preserve the full interpreted communication, with no injectivity
premise on any chosen assignment. -/
theorem InternalStep.interprets_of_communication {kind : InternalKind} {a b : Named V}
    (h : InternalStep kind a b) (hk : kind = .communication)
    (ρ : NameAssignment) (env : V → Ground) {p : Agent Empty}
    (ha : a.Interprets ρ env p) :
    ∃ q, Agent.Tau p q ∧ b.Interprets ρ env q := by
  induction h generalizing ρ p with
  | embed h =>
    cases hk
    exact h.communication_realizes ρ env ha
  | parLeft c h ih =>
    obtain ⟨r,s,hr,hs,he⟩ := ha
    obtain ⟨r',ht,hr'⟩ := ih hk ρ env hr
    obtain ⟨q,hq,he'⟩ := he.tau_transport (ht.parLeft s)
    exact ⟨q,hq,(hr'.par hs).congr he'⟩
  | parRight c h ih =>
    obtain ⟨r,s,hr,hs,he⟩ := ha
    obtain ⟨s',ht,hs'⟩ := ih hk ρ env hs
    obtain ⟨q,hq,he'⟩ := he.tau_transport (ht.parRight r)
    exact ⟨q,hq,(hr.par hs').congr he'⟩
  | newName n h ih =>
    obtain ⟨v,hv⟩ := ha
    obtain ⟨q,hq,hb⟩ := ih hk (Function.update ρ n v) env hv
    exact ⟨q,hq,v,hb⟩
  | newVar h ih =>
    obtain ⟨m,hm⟩ := ha
    obtain ⟨q,hq,hb⟩ := ih hk ρ (extendEnv env m) hm
    exact ⟨q,hq,m,hb⟩
  | congr hs h ht ih =>
    obtain ⟨q,hq,hb⟩ := ih hk ρ env ((hs.interprets ρ env p).mp ha)
    exact ⟨q,hq,(ht.interprets ρ env q).mp hb⟩

theorem InternalStep.communication_interprets {a b : Named V}
    (h : InternalStep .communication a b) (ρ : NameAssignment) (env : V → Ground)
    {p : Agent Empty} (ha : a.Interprets ρ env p) :
    ∃ q, Agent.Tau p q ∧ b.Interprets ρ env q := h.interprets_of_communication rfl ρ env ha

/-- Every actual reduction either has the interpreted Tau/target or admits a
classified conditional derivation. The conditional case remains open. -/
theorem Reduction.interprets_or_conditional {a b : Named V} (h : Reduction a b)
    (ρ : NameAssignment) (env : V → Ground) {p : Agent Empty}
    (ha : a.Interprets ρ env p) :
    (∃ q, Agent.Tau p q ∧ b.Interprets ρ env q) ∨
      ∃ taken, InternalStep (.conditional taken) a b := by
  obtain ⟨kind,hk⟩ := h.classify
  cases kind with
  | communication => exact .inl (hk.communication_interprets ρ env ha)
  | conditional taken => exact .inr ⟨taken,hk⟩

theorem InternalStep.communication_canonical (s : ScopedState restricted handles)
    {a b : Named (Fin handles)} (hs : Structural (restrictedState hidden s) a)
    (h : InternalStep .communication a b) :
    ∃ q : ScopedState restricted handles,
      ScopedStep hidden restricted s .tau q ∧ q.frame = s.frame ∧
      b.Interprets NameAssignment.literal q.frame.value q.body ∧
      b.RepresentsFrame hidden q.frame := by
  obtain ⟨q,hq,hb⟩ := h.communication_interprets NameAssignment.literal s.frame.value
    (hs.canonical_interprets s)
  exact ⟨⟨s.frame,q⟩,(scoped_tau_iff _ _).mpr ⟨rfl,hq⟩,rfl,hb,
    ((restrictedState_represents s).structural hs).internal h.reduction⟩

end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
