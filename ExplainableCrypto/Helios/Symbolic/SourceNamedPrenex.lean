import ExplainableCrypto.Helios.Symbolic.SourceNamePrefixStructure

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- Every finite Named process has an outer name prefix and one Extended body.
Parallel extrusion first freshens each prefix against the other component.
This is a structural representative, not a canonical active-frame theorem. -/
theorem exists_prenex (a : Named V) :
    ∃ (ns : List SourceName) (b : Extended V), Structural a (restrictNames ns (.embed b)) := by
  induction a with
  | embed a => exact ⟨[],a,.refl _⟩
  | newName n a ih =>
    obtain ⟨ns,b,hb⟩ := ih
    exact ⟨n::ns,b,.newName n hb⟩
  | newVar a ih =>
    obtain ⟨ns,b,hb⟩ := ih
    exact ⟨ns,.newVar b,(Structural.newVar hb).trans
      ((Structural.var_restrictNames (.embed b) ns).trans ((Structural.embedVar b).symm.restrictNames ns))⟩
  | par a b ha hb =>
    obtain ⟨ns,a',ha⟩ := ha
    obtain ⟨ns',e,k,hfresh,hfn⟩ := exists_fresh_extended_prefix ns a' b.allNames
    let a'' := a'.mapNames e k
    have hleft : Structural a (restrictNames ns' (.embed a'')) := ha.trans hfresh
    obtain ⟨ms,b',hb⟩ := hb
    obtain ⟨ms',e',k',hfresh',hfm⟩ := exists_fresh_extended_prefix ms b' (Named.embed a'').freeNames
    let b'' := b'.mapNames e' k'
    have hright : Structural b (restrictNames ms' (.embed b'')) := hb.trans hfresh'
    refine ⟨ns' ++ ms',.par a'' b'',?_⟩
    rw [restrictNames_append]
    apply (Structural.parLeft b hleft).trans
    apply (Structural.par_restrictNames_left (.embed a'') b ns' ?_).trans
    · apply Structural.restrictNames
      apply (Structural.parRight (.embed a'') hright).trans
      exact (Structural.par_restrictNames_right (.embed a'') (.embed b'') ms' hfm).trans
        ((Structural.embedPar a'' b'').symm.restrictNames ms')
    · intro n hn hf
      exact hfn n hn (freeNames_subset_allNames b hf)

/-- The outer prefix can additionally avoid any finite externally used set. -/
theorem exists_fresh_prenex (a : Named V) (avoid : Finset SourceName) :
    ∃ (ns : List SourceName) (b : Extended V), Structural a (restrictNames ns (.embed b)) ∧
      ∀ n ∈ ns, n ∉ avoid := by
  obtain ⟨ns,b,h⟩ := exists_prenex a
  obtain ⟨ns',e,k,he,hf⟩ := exists_fresh_extended_prefix ns b avoid
  exact ⟨ns',b.mapNames e k,h.trans he,hf⟩

theorem exists_distinct_fresh_prenex (a : Named V) (avoid : Finset SourceName) :
    ∃ (ns : List SourceName) (b : Extended V), Structural a (restrictNames ns (.embed b)) ∧
      ns.Nodup ∧ ∀ n ∈ ns, n ∉ avoid := by
  obtain ⟨ns,b,h⟩ := exists_prenex a
  obtain ⟨ns',e,k,he,_,hf,hn,_⟩ := exists_common_fresh_prefix ns (.embed b) (.embed b) avoid
  exact ⟨ns',b.mapNames e k,h.trans he,hn,hf⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
