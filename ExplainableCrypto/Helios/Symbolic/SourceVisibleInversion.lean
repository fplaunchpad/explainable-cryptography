import ExplainableCrypto.Helios.Symbolic.SourceVisibleElection

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent

theorem Visible.input_context {p q : Agent Empty} {c : Nat} {m : Ground} (h : Visible p (.input c m) q) :
    ∃ body : Agent (Option Empty), ∃ context : Agent Empty,
      p.threads = (Agent.input c body).threads+context.threads ∧
      q.threads = (body.bind m).threads+context.threads := by
  obtain ⟨x,y,context,hp,hx,hy⟩ := (visible_iff_threads _ _ _).mp h
  cases hp with
  | input _ _ body => exact ⟨body,context,hx,hy⟩

theorem Visible.output_context {p q : Agent Empty} {c : Nat} {m : Ground} (h : Visible p (.output c m) q) :
    ∃ body context : Agent Empty,
      p.threads = (Agent.output c m body).threads+context.threads ∧
      q.threads = body.threads+context.threads := by
  obtain ⟨x,y,context,hp,hx,hy⟩ := (visible_iff_threads _ _ _).mp h
  cases hp with
  | output => exact ⟨y,context,hx,hy⟩

/-- Uniqueness is of the complete active continuation, not just its channel.
Multiset cancellation preserves the untouched parallel context. -/
theorem visible_input_deterministic {p q q' : Agent Empty} {c : Nat} {m : Ground}
    (h : Visible p (.input c m) q) (h' : Visible p (.input c m) q')
    (hu : ∀ a b : Agent (Option Empty), Agent.input c a ∈ p.threads → Agent.input c b ∈ p.threads → a=b) :
    ParEq q q' := by
  obtain ⟨body,context,hp,hq⟩ := h.input_context
  obtain ⟨body',context',hp',hq'⟩ := h'.input_context
  have hm : Agent.input c body ∈ p.threads := by rw [hp]; simp [threads,threadList]
  have hm' : Agent.input c body' ∈ p.threads := by rw [hp']; simp [threads,threadList]
  obtain rfl := hu body body' hm hm'
  have he : context.threads=context'.threads := add_left_cancel (hp.symm.trans hp')
  exact (parEq_iff_threads _ _).mpr (by rw [hq,hq',he])

theorem visible_output_deterministic {p q q' : Agent Empty} {c : Nat} {m : Ground}
    (h : Visible p (.output c m) q) (h' : Visible p (.output c m) q')
    (hu : ∀ a b : Agent Empty, Agent.output c m a ∈ p.threads → Agent.output c m b ∈ p.threads → a=b) :
    ParEq q q' := by
  obtain ⟨body,context,hp,hq⟩ := h.output_context
  obtain ⟨body',context',hp',hq'⟩ := h'.output_context
  have hm : Agent.output c m body ∈ p.threads := by rw [hp]; simp [threads,threadList]
  have hm' : Agent.output c m body' ∈ p.threads := by rw [hp']; simp [threads,threadList]
  obtain rfl := hu body body' hm hm'
  have he : context.threads=context'.threads := add_left_cancel (hp.symm.trans hp')
  exact (parEq_iff_threads _ _).mpr (by rw [hq,hq',he])
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
