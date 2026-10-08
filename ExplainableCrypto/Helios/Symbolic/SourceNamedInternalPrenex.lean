import ExplainableCrypto.Helios.Symbolic.SourcePairedPrenex

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- One actual Extended reduction witnesses every Named internal step.
The same outer name prefix represents both endpoints, even after arbitrary
Named Struct paths; no canonical-frame or realization premise is assumed. -/
theorem Reduction.prenex {a b : Named V} (h : Reduction a b) :
    ∃ (ns : List SourceName) (a' b' : Extended V),
      Structural a (Named.restrictNames ns (.embed a')) ∧
      Structural b (Named.restrictNames ns (.embed b')) ∧ Extended.Reduction a' b' := by
  induction h with
  | embed h => exact ⟨[],_,_,.refl _,.refl _,h⟩
  | newName n h ih =>
    obtain ⟨ns,a',b',ha,hb,hr⟩ := ih
    exact ⟨n::ns,a',b',.newName n ha,.newName n hb,hr⟩
  | newVar h ih =>
    obtain ⟨ns,a',b',ha,hb,hr⟩ := ih
    refine ⟨ns,.newVar a',.newVar b',?_,?_,.newVar hr⟩
    · exact (Structural.newVar ha).trans ((Structural.var_restrictNames _ ns).trans
        ((Structural.embedVar a').symm.restrictNames ns))
    · exact (Structural.newVar hb).trans ((Structural.var_restrictNames _ ns).trans
        ((Structural.embedVar b').symm.restrictNames ns))
  | parLeft d h ih =>
    obtain ⟨ns,a',b',ha,hb,hr⟩ := ih
    obtain ⟨ns',e,k,d',ha',hb',_,_⟩ := parallel_prenex_pair ns a' b' d ∅ (by simp)
    exact ⟨ns',_,_,(Structural.parLeft d ha).trans ha',(Structural.parLeft d hb).trans hb',
      .parLeft d' (hr.mapNames e k)⟩
  | parRight d h ih =>
    obtain ⟨ns,a',b',ha,hb,hr⟩ := ih
    obtain ⟨ns',e,k,d',ha',hb',_,_⟩ := parallel_prenex_pair ns a' b' d ∅ (by simp)
    exact ⟨ns',_,_,(Structural.comm _ _).trans ((Structural.parLeft d ha).trans ha'),
      (Structural.comm _ _).trans ((Structural.parLeft d hb).trans hb'),.parLeft d' (hr.mapNames e k)⟩
  | congr hs h ht ih =>
    obtain ⟨ns,a',b',ha,hb,hr⟩ := ih
    exact ⟨ns,a',b',hs.trans ha,ht.symm.trans hb,hr⟩

theorem reduction_iff_prenex (a b : Named V) : Reduction a b ↔
    ∃ (ns : List SourceName) (a' b' : Extended V),
      Structural a (Named.restrictNames ns (.embed a')) ∧
      Structural b (Named.restrictNames ns (.embed b')) ∧ Extended.Reduction a' b' := by
  constructor
  · exact fun h => h.prenex
  · rintro ⟨ns,a',b',ha,hb,hr⟩
    exact .congr ha ((Reduction.embed hr).restrictNames ns) hb.symm

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
