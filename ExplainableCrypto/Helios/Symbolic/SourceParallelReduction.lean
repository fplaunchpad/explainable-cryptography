import ExplainableCrypto.Helios.Symbolic.SourceParallelStructure

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent

theorem PrimitiveStep.core {p q : Agent Empty} (h : PrimitiveStep p q) : CoreStep p q := by
  cases h with
  | comm => exact .comm _ _ _ _
  | thenBranch _ _ _ h => exact .thenBranch _ _ _ h
  | elseBranch _ _ _ h => exact .elseBranch _ _ _ h

theorem Tau.of_core {p q : Agent Empty} (h : CoreStep p q) : Tau p q :=
  ⟨p,q,.refl _,h,.refl _⟩

theorem Tau.congr {p p' q q' : Agent Empty} (hp : ParEq p' p) (h : Tau p q) (hq : ParEq q q') :
    Tau p' q' := by
  obtain ⟨a,b,ha,hh,hb⟩ := h
  exact ⟨a,b,hp.trans ha,hh,hb.trans hq⟩

theorem Tau.parLeft {p q : Agent Empty} (h : Tau p q) (r : Agent Empty) :
    Tau (.par p r) (.par q r) := by
  obtain ⟨a,b,ha,hh,hb⟩ := h
  exact ⟨.par a r,.par b r,.par ha (.refl _),.parLeft _ hh,.par hb (.refl _)⟩

theorem Tau.parRight (r : Agent Empty) {p q : Agent Empty} (h : Tau p q) :
    Tau (.par r p) (.par r q) := by
  obtain ⟨a,b,ha,hh,hb⟩ := h
  exact ⟨.par r a,.par r b,.par (.refl _) ha,.parRight _ hh,.par (.refl _) hb⟩

theorem ThreadReduction.add_context {before after : Multiset (Agent Empty)}
    (h : ThreadReduction before after) (r : Agent Empty) :
    ThreadReduction (before+r.threads) (after+r.threads) := by
  obtain ⟨p,q,context,hp,hb,ha⟩ := h
  refine ⟨p,q,.par context r,hp,?_,?_⟩ <;>
    simp only [hb,ha,threads_par,add_assoc]

/-- All core contexts extract to one primitive redex and an unchanged remainder. -/
theorem CoreStep.threadReduction {p q : Agent Empty} (h : CoreStep p q) :
    ThreadReduction p.threads q.threads := by
  induction h with
  | comm c m p q =>
    exact ⟨_,_,.nil,.comm c m p q,by simp only [threads_nil,add_zero],by simp only [threads_nil,add_zero]⟩
  | thenBranch f p q hf =>
    exact ⟨_,_,.nil,.thenBranch f p q hf,by simp only [threads_nil,add_zero],by simp only [threads_nil,add_zero]⟩
  | elseBranch f p q hf =>
    exact ⟨_,_,.nil,.elseBranch f p q hf,by simp only [threads_nil,add_zero],by simp only [threads_nil,add_zero]⟩
  | parLeft r _ ih => exact ih.add_context r
  | parRight r _ ih => simpa only [threads_par,add_comm] using ih.add_context r

/-- Complete internal-step characterization for the parallel structural layer.
The converse constructs an actual core step in a real process context. -/
theorem tau_iff_threadReduction (p q : Agent Empty) :
    Tau p q ↔ ThreadReduction p.threads q.threads := by
  constructor
  · rintro ⟨a,b,ha,h,hb⟩
    have ht := h.threadReduction
    rw [← ha.threads_eq,hb.threads_eq] at ht
    exact ht
  · rintro ⟨a,b,context,h,ha,hb⟩
    refine ⟨.par a context,.par b context,?_,.parLeft context h.core,?_⟩
    · exact (parEq_iff_threads _ _).mpr ha
    · exact (parEq_iff_threads _ _).mpr hb.symm
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
