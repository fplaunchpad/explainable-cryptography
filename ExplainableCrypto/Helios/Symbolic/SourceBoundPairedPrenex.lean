import ExplainableCrypto.Helios.Symbolic.SourceNamedVariableRename

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- A bound-output pair has different variable domains at its endpoints. The
same old context is represented at the source and shifted through Some at the
target; only the acting bodies need the shared fresh name permutation. -/
theorem bound_parallel_prenex_pair (ns : List SourceName) (a : Extended V)
    (b : Extended (Option V)) (d : Named V) (avoid : Finset SourceName)
    (hf : ∀ n ∈ ns, n ∉ avoid) :
    ∃ (ns' : List SourceName) (e k : Nat ≃ Nat) (d' : Extended V),
      Structural (.par (restrictNames ns (.embed a)) d)
        (restrictNames ns' (.embed (.par (a.mapNames e k) d'))) ∧
      Structural (.par (restrictNames ns (.embed b)) (d.rename some))
        (restrictNames ns' (.embed (.par (b.mapNames e k) (d'.rename some)))) ∧
      (∀ n ∈ ns', n ∉ avoid) ∧ ∀ n ∈ avoid, n.map e k = n := by
  obtain ⟨ns',e,k,ha,hb,hn,_,_,_,hfix⟩ := exists_common_fresh_prefix ns (.embed a) (.embed b)
    (d.allNames ∪ avoid)
  obtain ⟨ms,d',hd,hm⟩ := exists_fresh_prenex d
    (avoid ∪ ((Named.embed (a.mapNames e k)).freeNames ∪ (Named.embed (b.mapNames e k)).freeNames))
  have hds : Structural (d.rename some) (restrictNames ms (.embed (d'.rename some))) := by
    simpa only [restrictNames_rename,Named.rename] using hd.rename some (Option.some_injective _)
  have hdFresh : ∀ n ∈ ns', n ∉ d.freeNames := by
    intro n hmem hfree
    exact hn n hmem (Finset.mem_union_left _ (freeNames_subset_allNames d hfree))
  have hdsFresh : ∀ n ∈ ns', n ∉ (d.rename some).freeNames := by
    simpa only [freeNames_rename] using hdFresh
  have haFresh : ∀ n ∈ ms, n ∉ (Named.embed (a.mapNames e k)).freeNames := by
    intro n hmem hfree
    exact hm n hmem (Finset.mem_union_right _ (Finset.mem_union_left _ hfree))
  have hbFresh : ∀ n ∈ ms, n ∉ (Named.embed (b.mapNames e k)).freeNames := by
    intro n hmem hfree
    exact hm n hmem (Finset.mem_union_right _ (Finset.mem_union_right _ hfree))
  refine ⟨ns' ++ ms,e,k,d',?_,?_,?_,?_⟩
  · exact (Structural.parLeft d ha).trans (Structural.par_prefix_combine ns' ms _ d' d hd hdFresh haFresh)
  · exact (Structural.parLeft (d.rename some) hb).trans
      (Structural.par_prefix_combine ns' ms _ (d'.rename some) (d.rename some) hds hdsFresh hbFresh)
  · intro n hmem hav
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hn n hmem (Finset.mem_union_right _ hav)
    · exact hm n hmem (Finset.mem_union_left _ hav)
  · intro n hav
    exact hfix n (Finset.mem_union_right _ hav) (fun hmem => hf n hmem hav)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
