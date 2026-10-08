import ExplainableCrypto.Helios.Symbolic.SourceNamedPrenex

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

theorem Structural.par_prefix_combine (ns ms : List SourceName) (a b : Extended V) (d : Named V)
    (hd : Structural d (Named.restrictNames ms (.embed b)))
    (hn : ∀ n ∈ ns, n ∉ d.freeNames) (hm : ∀ n ∈ ms, n ∉ (Named.embed a).freeNames) :
    Structural (.par (Named.restrictNames ns (.embed a)) d)
      (Named.restrictNames (ns ++ ms) (.embed (.par a b))) := by
  rw [restrictNames_append]
  apply (Structural.par_restrictNames_left (.embed a) d ns hn).trans
  apply Structural.restrictNames
  exact (Structural.parRight (.embed a) hd).trans
    ((Structural.par_restrictNames_right (.embed a) (.embed b) ms hm).trans
      ((Structural.embedPar a b).symm.restrictNames ms))

/-- Both endpoints share one context body and the same name permutations.
Names protected by the original prefix's freshness stay fixed, so this helper
can preserve an entire visible label while moving both endpoints coherently. -/
theorem parallel_prenex_pair (ns : List SourceName) (a b : Extended V) (d : Named V)
    (avoid : Finset SourceName) (hf : ∀ n ∈ ns, n ∉ avoid) :
    ∃ (ns' : List SourceName) (e k : Nat ≃ Nat) (d' : Extended V),
      Structural (.par (restrictNames ns (.embed a)) d)
        (restrictNames ns' (.embed (.par (a.mapNames e k) d'))) ∧
      Structural (.par (restrictNames ns (.embed b)) d)
        (restrictNames ns' (.embed (.par (b.mapNames e k) d'))) ∧
      (∀ n ∈ ns', n ∉ avoid) ∧ ∀ n ∈ avoid, n.map e k = n := by
  obtain ⟨ns',e,k,ha,hb,hn,_,_,_,hfix⟩ := exists_common_fresh_prefix ns (.embed a) (.embed b)
    (d.allNames ∪ avoid)
  obtain ⟨ms,d',hd,hm⟩ := exists_fresh_prenex d
    (avoid ∪ ((Named.embed (a.mapNames e k)).freeNames ∪ (Named.embed (b.mapNames e k)).freeNames))
  have hdFresh : ∀ n ∈ ns', n ∉ d.freeNames := by
    intro n hmem hfree
    exact hn n hmem (Finset.mem_union_left _ (freeNames_subset_allNames d hfree))
  have haFresh : ∀ n ∈ ms, n ∉ (Named.embed (a.mapNames e k)).freeNames := by
    intro n hmem hfree
    exact hm n hmem (Finset.mem_union_right _ (Finset.mem_union_left _ hfree))
  have hbFresh : ∀ n ∈ ms, n ∉ (Named.embed (b.mapNames e k)).freeNames := by
    intro n hmem hfree
    exact hm n hmem (Finset.mem_union_right _ (Finset.mem_union_right _ hfree))
  refine ⟨ns' ++ ms,e,k,d',?_,?_,?_,?_⟩
  · exact (Structural.parLeft d ha).trans (Structural.par_prefix_combine ns' ms _ d' d hd hdFresh haFresh)
  · exact (Structural.parLeft d hb).trans (Structural.par_prefix_combine ns' ms _ d' d hd hdFresh hbFresh)
  · intro n hmem hav
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hn n hmem (Finset.mem_union_right _ hav)
    · exact hm n hmem (Finset.mem_union_left _ hav)
  · intro n hav
    exact hfix n (Finset.mem_union_right _ hav) (fun hmem => hf n hmem hav)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
