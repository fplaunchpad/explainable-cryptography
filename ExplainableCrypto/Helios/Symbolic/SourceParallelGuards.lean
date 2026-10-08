import ExplainableCrypto.Helios.Symbolic.SourceParallelReduction

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent

/-- Necessary readiness in the actual active threads, even after arbitrary
parallel rearrangement and insertion/removal of null components. -/
def Enabled (p : Agent Empty) : Prop :=
  (∃ f a b, Agent.branch f a b ∈ p.threads) ∨
  (∃ c m a b, Agent.output c m a ∈ p.threads ∧ Agent.input c b ∈ p.threads)

theorem PrimitiveStep.enabled {p q : Agent Empty} (h : PrimitiveStep p q) : Enabled p := by
  cases h <;> simp [Enabled,threads,threadList]

theorem Tau.enabled {p q : Agent Empty} (h : Tau p q) : Enabled p := by
  obtain ⟨a,b,context,hp,ha,_⟩ := (tau_iff_threadReduction p q).mp h
  rcases hp.enabled with ⟨f,x,y,hm⟩ | ⟨c,m,x,y,ho,hi⟩
  · refine .inl ⟨f,x,y,?_⟩
    rw [ha]
    exact Multiset.mem_add.mpr (.inl hm)
  · refine .inr ⟨c,m,x,y,?_,?_⟩ <;> rw [ha]
    · exact Multiset.mem_add.mpr (.inl ho)
    · exact Multiset.mem_add.mpr (.inl hi)

theorem tau_nil_no_step (q : Agent Empty) : ¬ Tau .nil q := by
  intro h
  rcases h.enabled with ⟨f,a,b,hm⟩ | ⟨c,m,a,b,hm,_⟩ <;> simp [threads,threadList] at hm

theorem tau_input_no_step (c : Nat) (p : Agent (Option Empty)) (q : Agent Empty) :
    ¬ Tau (.input c p) q := by
  intro h
  rcases h.enabled with ⟨f,a,b,hm⟩ | ⟨d,m,a,b,hm,_⟩ <;> simp [threads,threadList] at hm

theorem tau_output_no_step (c : Nat) (m : Ground) (p q : Agent Empty) :
    ¬ Tau (.output c m p) q := by
  intro h
  rcases h.enabled with ⟨f,a,b,hm⟩ | ⟨d,t,a,b,_,hm⟩ <;> simp [threads,threadList] at hm
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
