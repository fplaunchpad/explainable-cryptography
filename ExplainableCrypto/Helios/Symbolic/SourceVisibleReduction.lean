import ExplainableCrypto.Helios.Symbolic.SourceVisibleSyntax

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent

theorem PrimitiveVisible.core {p q : Agent Empty} {a : PayloadEvent} (h : PrimitiveVisible p a q) :
    CoreVisible p a q := by
  cases h with
  | input => exact .input _ _ _
  | output => exact .output _ _ _

theorem Visible.of_core {p q : Agent Empty} {a : PayloadEvent} (h : CoreVisible p a q) : Visible p a q :=
  ⟨p,q,.refl _,h,.refl _⟩

theorem Visible.congr {p p' q q' : Agent Empty} {a : PayloadEvent}
    (hp : ParEq p' p) (h : Visible p a q) (hq : ParEq q q') : Visible p' a q' := by
  obtain ⟨r,s,hr,hh,hs⟩ := h
  exact ⟨r,s,hp.trans hr,hh,hs.trans hq⟩

theorem Visible.parLeft {p q : Agent Empty} {a : PayloadEvent} (h : Visible p a q) (r : Agent Empty) :
    Visible (.par p r) a (.par q r) := by
  obtain ⟨x,y,hx,hh,hy⟩ := h
  exact ⟨.par x r,.par y r,.par hx (.refl _),.parLeft _ hh,.par hy (.refl _)⟩

theorem Visible.parRight (r : Agent Empty) {p q : Agent Empty} {a : PayloadEvent} (h : Visible p a q) :
    Visible (.par r p) a (.par r q) := by
  obtain ⟨x,y,hx,hh,hy⟩ := h
  exact ⟨.par r x,.par r y,.par (.refl _) hx,.parRight _ hh,.par (.refl _) hy⟩

theorem VisibleThreads.add_context {before after : Multiset (Agent Empty)} {a : PayloadEvent}
    (h : VisibleThreads before a after) (r : Agent Empty) :
    VisibleThreads (before+r.threads) a (after+r.threads) := by
  obtain ⟨p,q,context,hp,hb,ha⟩ := h
  refine ⟨p,q,.par context r,hp,?_,?_⟩ <;> simp only [hb,ha,threads_par,add_assoc]

theorem CoreVisible.threads {p q : Agent Empty} {a : PayloadEvent} (h : CoreVisible p a q) :
    VisibleThreads p.threads a q.threads := by
  induction h with
  | input c m body =>
    exact ⟨_,_,.nil,.input c m body,by simp only [threads_nil,add_zero],by simp only [threads_nil,add_zero]⟩
  | output c m p =>
    exact ⟨_,_,.nil,.output c m p,by simp only [threads_nil,add_zero],by simp only [threads_nil,add_zero]⟩
  | parLeft r _ ih => exact ih.add_context r
  | parRight r _ ih => simpa only [threads_par,add_comm] using ih.add_context r

/-- Exact active-prefix/context characterization, with an unchanged real
parallel context on both sides. It preserves the full event and payload. -/
theorem visible_iff_threads (p q : Agent Empty) (a : PayloadEvent) :
    Visible p a q ↔ VisibleThreads p.threads a q.threads := by
  constructor
  · rintro ⟨x,y,hx,h,hy⟩
    have ht := h.threads
    rw [← hx.threads_eq,hy.threads_eq] at ht
    exact ht
  · rintro ⟨x,y,context,h,hx,hy⟩
    exact ⟨.par x context,.par y context,(parEq_iff_threads _ _).mpr hx,
      .parLeft context h.core,(parEq_iff_threads _ _).mpr hy.symm⟩

theorem Visible.input_prefix {p q : Agent Empty} {c : Nat} {m : Ground} (h : Visible p (.input c m) q) :
    ∃ body : Agent (Option Empty), Agent.input c body ∈ p.threads := by
  obtain ⟨x,y,context,hp,hx,_⟩ := (visible_iff_threads _ _ _).mp h
  cases hp with
  | input _ _ body =>
    refine ⟨body,?_⟩
    rw [hx]
    simp [Agent.threads,threadList]

theorem Visible.output_prefix {p q : Agent Empty} {c : Nat} {m : Ground} (h : Visible p (.output c m) q) :
    ∃ body : Agent Empty, Agent.output c m body ∈ p.threads := by
  obtain ⟨x,y,context,hp,hx,_⟩ := (visible_iff_threads _ _ _).mp h
  cases hp with
  | output =>
    refine ⟨y,?_⟩
    rw [hx]
    simp [Agent.threads,threadList]
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
