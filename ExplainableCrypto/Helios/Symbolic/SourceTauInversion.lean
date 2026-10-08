import ExplainableCrypto.Helios.Symbolic.SourceParallelGuards

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent

/-- Explicit redex cases, retaining both the consumed prefixes and unchanged
context. This is the complete thread-reduction characterization unpacked. -/
theorem Tau.cases {p q : Agent Empty} (h : Tau p q) :
    (∃ c m a b context, p.threads = (Agent.par (.output c m a) (.input c b)).threads + threads context ∧
      q.threads = (Agent.par a (b.bind m)).threads + threads context) ∨
    (∃ f a b context, f.Holds Empty.elim ∧ p.threads = (Agent.branch f a b).threads + threads context ∧
      q.threads = a.threads + threads context) ∨
    (∃ f a b context, ¬ f.Holds Empty.elim ∧ p.threads = (Agent.branch f a b).threads + threads context ∧
      q.threads = b.threads + threads context) := by
  obtain ⟨a,b,context,hp,ha,hb⟩ := (tau_iff_threadReduction p q).mp h
  cases hp with
  | comm => exact .inl ⟨_,_,_,_,context,ha,hb⟩
  | thenBranch _ _ _ hf => exact .inr (.inl ⟨_,_,_,context,hf,ha,hb⟩)
  | elseBranch _ _ _ hf => exact .inr (.inr ⟨_,_,_,context,hf,ha,hb⟩)

/-- All possible matching pairs have these exact continuations and payload.
This does not assert that the pair exists; live cases supply an actual Tau. -/
def OnlyCommunication (p : Agent Empty) (c : Nat) (m : Ground)
    (a : Agent Empty) (b : Agent (Option Empty)) : Prop :=
  ∀ d t x y, Agent.output d t x ∈ p.threads → Agent.input d y ∈ p.threads →
    d=c ∧ t=m ∧ x=a ∧ y=b

def NoConditional (p : Agent Empty) : Prop := ∀ f a b, Agent.branch f a b ∉ p.threads

theorem Tau.only_communication {p q : Agent Empty} (h : Tau p q)
    (hn : NoConditional p) {c : Nat} {m : Ground} {a : Agent Empty} {b : Agent (Option Empty)}
    (hu : OnlyCommunication p c m a b) :
    ∃ context : Agent Empty,
      p.threads = (Agent.par (.output c m a) (.input c b)).threads + context.threads ∧
      q.threads = (Agent.par a (b.bind m)).threads + context.threads := by
  rcases h.cases with ⟨d,t,x,y,context,hp,hq⟩ | ⟨f,x,y,context,_,hp,_⟩ | ⟨f,x,y,context,_,hp,_⟩
  · have ho : Agent.output d t x ∈ p.threads := by rw [hp]; simp [threads,threadList]
    have hi : Agent.input d y ∈ p.threads := by rw [hp]; simp [threads,threadList]
    obtain ⟨rfl,rfl,rfl,rfl⟩ := hu d t x y ho hi
    exact ⟨context,hp,hq⟩
  all_goals
    have hm : Agent.branch f x y ∈ p.threads := by rw [hp]; simp [threads,threadList]
    exact (hn f x y hm).elim

/-- Uniqueness of the consumed pair forces uniqueness of the entire residual,
including the untouched context, by cancellativity of thread multisets. -/
theorem tau_deterministic_communication {p q r : Agent Empty} (h : Tau p q) (h' : Tau p r)
    (hn : NoConditional p) {c : Nat} {m : Ground} {a : Agent Empty} {b : Agent (Option Empty)}
    (hu : OnlyCommunication p c m a b) : ParEq q r := by
  obtain ⟨context,hp,hq⟩ := h.only_communication hn hu
  obtain ⟨context',hp',hr⟩ := h'.only_communication hn hu
  have he : context.threads=context'.threads := add_left_cancel (hp.symm.trans hp')
  apply (parEq_iff_threads _ _).mpr
  rw [hq,hr,he]

/-- A single conditional may coexist with input-only waiting processes. -/
def OnlyConditional (p : Agent Empty) (f : Formula Empty) (a b : Agent Empty) : Prop :=
  (∀ c m q, Agent.output c m q ∉ p.threads) ∧
  (∀ g x y, Agent.branch g x y ∈ p.threads → g=f ∧ x=a ∧ y=b)

theorem Tau.only_conditional {p q : Agent Empty} (h : Tau p q)
    {f : Formula Empty} {a b : Agent Empty} (hu : OnlyConditional p f a b) :
    (f.Holds Empty.elim ∧ ∃ context : Agent Empty,
      p.threads = (Agent.branch f a b).threads + context.threads ∧ q.threads = a.threads + context.threads) ∨
    (¬ f.Holds Empty.elim ∧ ∃ context : Agent Empty,
      p.threads = (Agent.branch f a b).threads + context.threads ∧ q.threads = b.threads + context.threads) := by
  rcases h.cases with ⟨d,t,x,y,context,hp,_⟩ | ⟨g,x,y,context,hg,hp,hq⟩ | ⟨g,x,y,context,hg,hp,hq⟩
  · have hm : Agent.output d t x ∈ p.threads := by rw [hp]; simp [threads,threadList]
    exact (hu.1 d t x hm).elim
  · have hm : Agent.branch g x y ∈ p.threads := by rw [hp]; simp [threads,threadList]
    obtain ⟨rfl,rfl,rfl⟩ := hu.2 g x y hm
    exact .inl ⟨hg,context,hp,hq⟩
  · have hm : Agent.branch g x y ∈ p.threads := by rw [hp]; simp [threads,threadList]
    obtain ⟨rfl,rfl,rfl⟩ := hu.2 g x y hm
    exact .inr ⟨hg,context,hp,hq⟩

theorem tau_deterministic_conditional {p q r : Agent Empty} (h : Tau p q) (h' : Tau p r)
    {f : Formula Empty} {a b : Agent Empty} (hu : OnlyConditional p f a b) : ParEq q r := by
  rcases h.only_conditional hu with ⟨hf,context,hp,hq⟩ | ⟨hf,context,hp,hq⟩ <;>
    rcases h'.only_conditional hu with ⟨hf',context',hp',hr⟩ | ⟨hf',context',hp',hr⟩
  · have he : context.threads=context'.threads := add_left_cancel (hp.symm.trans hp')
    exact (parEq_iff_threads _ _).mpr (by rw [hq,hr,he])
  · exact (hf' hf).elim
  · exact (hf hf').elim
  · have he : context.threads=context'.threads := add_left_cancel (hp.symm.trans hp')
    exact (parEq_iff_threads _ _).mpr (by rw [hq,hr,he])
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
