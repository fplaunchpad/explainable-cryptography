import ExplainableCrypto.Helios.Symbolic.SourceNamedFreePrenex

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- A single internal action has a common distinct prefix avoiding any finite
external name set. Both endpoint bodies use the same fresh permutation. -/
theorem Reduction.fresh_prenex {a b : Named V} (h : Reduction a b) (avoid : Finset SourceName) :
    ∃ (ns : List SourceName) (a' b' : Extended V),
      Structural a (Named.restrictNames ns (.embed a')) ∧
      Structural b (Named.restrictNames ns (.embed b')) ∧ Extended.Reduction a' b' ∧
      ns.Nodup ∧ ∀ n ∈ ns, n ∉ avoid := by
  obtain ⟨ns,a',b',ha,hb,hr⟩ := h.prenex
  obtain ⟨ns',e,k,ha',hb',hn,hd,_⟩ := exists_common_fresh_prefix ns (.embed a') (.embed b') avoid
  exact ⟨ns',_,_,ha.trans ha',hb.trans hb',hr.mapNames e k,hd,hn⟩

/-- Free-action factorization can avoid the other world's finite support while
retaining exactly the same original label, including all input-recipe names. -/
theorem FreeStep.fresh_prenex {a b : Named V} {l : Extended.FreeLabel V}
    (h : FreeStep a l b) (avoid : Finset SourceName) :
    ∃ (ns : List SourceName) (a' b' : Extended V),
      Structural a (Named.restrictNames ns (.embed a')) ∧
      Structural b (Named.restrictNames ns (.embed b')) ∧ Extended.FreeStep a' l b' ∧
      ns.Nodup ∧ ∀ n ∈ ns, n ∉ avoid ∪ l.nameSupport := by
  obtain ⟨ns,a',b',ha,hb,hr,hn⟩ := h.prenex
  obtain ⟨ns',e,k,ha',hb',hn',hd,_,_,hfix⟩ := exists_common_fresh_prefix ns (.embed a') (.embed b')
    (avoid ∪ l.nameSupport)
  have hl : l.mapNames e k = l := l.mapNames_eq_of_fixed e k (by
    intro n hmem
    exact hfix n (Finset.mem_union_right _ hmem) (fun hns => hn n hns hmem))
  have hr' := hr.mapNames e k
  rw [hl] at hr'
  exact ⟨ns',_,_,ha.trans ha',hb.trans hb',hr',hd,hn'⟩

/-- Interpretation applies to the factored Extended source. Establishing the
right realization from a different canonical Named representative remains a
separate obligation; this statement does not silently assume that transfer. -/
theorem Reduction.prenex_interpreted {a b : Named V} (h : Reduction a b) :
    ∃ (ns : List SourceName) (a' b' : Extended V),
      Structural a (Named.restrictNames ns (.embed a')) ∧
      Structural b (Named.restrictNames ns (.embed b')) ∧ Extended.Reduction a' b' ∧
      ∀ (env : V → Ground) (p : Agent Empty), a'.Realizes env p →
        ∃ q, Agent.Tau p q ∧ b'.Realizes env q := by
  obtain ⟨ns,a',b',ha,hb,hr⟩ := h.prenex
  exact ⟨ns,a',b',ha,hb,hr,fun env _ hp => hr.realizes env hp⟩

theorem FreeStep.prenex_interpreted {a b : Named V} {l : Extended.FreeLabel V} (h : FreeStep a l b) :
    ∃ (ns : List SourceName) (a' b' : Extended V),
      Structural a (Named.restrictNames ns (.embed a')) ∧
      Structural b (Named.restrictNames ns (.embed b')) ∧ Extended.FreeStep a' l b' ∧
      (∀ n ∈ ns, n ∉ l.nameSupport) ∧
      ∀ (env : V → Ground) (p : Agent Empty), a'.Realizes env p →
        ∃ q, l.RealizedStep env p q ∧ b'.Realizes env q := by
  obtain ⟨ns,a',b',ha,hb,hr,hn⟩ := h.prenex
  exact ⟨ns,a',b',ha,hb,hr,hn,fun env _ hp => hr.realizes env hp⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
