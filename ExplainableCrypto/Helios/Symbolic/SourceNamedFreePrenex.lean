import ExplainableCrypto.Helios.Symbolic.SourceFixedLabelNames

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- Every Named free action factors through one common name prefix and an
Extended action with exactly its original label. The complete prefix is fresh
for that label, including every nested input-recipe name. -/
theorem FreeStep.prenex {a b : Named V} {l : Extended.FreeLabel V} (h : FreeStep a l b) :
    ∃ (ns : List SourceName) (a' b' : Extended V),
      Structural a (Named.restrictNames ns (.embed a')) ∧
      Structural b (Named.restrictNames ns (.embed b')) ∧ Extended.FreeStep a' l b' ∧
      ∀ n ∈ ns, n ∉ l.nameSupport := by
  induction h with
  | embed h => exact ⟨[],_,_,.refl _,.refl _,h,by simp⟩
  | scopeName n hf h ih =>
    obtain ⟨ns,a',b',ha,hb,hr,hn⟩ := ih
    refine ⟨n::ns,a',b',.newName n ha,.newName n hb,hr,?_⟩
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hf
    · exact hn m hm
  | scopeInput h ih =>
    obtain ⟨ns,a',b',ha,hb,hr,hn⟩ := ih
    refine ⟨ns,.newVar a',.newVar b',?_,?_,.scopeInput hr,?_⟩
    · exact (Structural.newVar ha).trans ((Structural.var_restrictNames _ ns).trans
        ((Structural.embedVar a').symm.restrictNames ns))
    · exact (Structural.newVar hb).trans ((Structural.var_restrictNames _ ns).trans
        ((Structural.embedVar b').symm.restrictNames ns))
    · simpa only [Extended.FreeLabel.input_shift_nameSupport] using hn
  | scopeOutput h ih =>
    obtain ⟨ns,a',b',ha,hb,hr,hn⟩ := ih
    refine ⟨ns,.newVar a',.newVar b',?_,?_,.scopeOutput hr,hn⟩
    · exact (Structural.newVar ha).trans ((Structural.var_restrictNames _ ns).trans
        ((Structural.embedVar a').symm.restrictNames ns))
    · exact (Structural.newVar hb).trans ((Structural.var_restrictNames _ ns).trans
        ((Structural.embedVar b').symm.restrictNames ns))
  | parLeft d h ih =>
    obtain ⟨ns,a',b',ha,hb,hr,hn⟩ := ih
    obtain ⟨ns',e,k,d',ha',hb',hn',hfix⟩ := parallel_prenex_pair ns a' b' d _ hn
    have he := hr.mapNames e k
    rw [Extended.FreeLabel.mapNames_eq_of_fixed _ e k hfix] at he
    exact ⟨ns',_,_,(Structural.parLeft d ha).trans ha',(Structural.parLeft d hb).trans hb',
      .parLeft d' he,hn'⟩
  | parRight d h ih =>
    obtain ⟨ns,a',b',ha,hb,hr,hn⟩ := ih
    obtain ⟨ns',e,k,d',ha',hb',hn',hfix⟩ := parallel_prenex_pair ns a' b' d _ hn
    have he := hr.mapNames e k
    rw [Extended.FreeLabel.mapNames_eq_of_fixed _ e k hfix] at he
    exact ⟨ns',_,_,(Structural.comm _ _).trans ((Structural.parLeft d ha).trans ha'),
      (Structural.comm _ _).trans ((Structural.parLeft d hb).trans hb'),.parLeft d' he,hn'⟩
  | congr hs h ht ih =>
    obtain ⟨ns,a',b',ha,hb,hr,hn⟩ := ih
    exact ⟨ns,a',b',hs.trans ha,ht.symm.trans hb,hr,hn⟩

theorem freeStep_iff_prenex (a b : Named V) (l : Extended.FreeLabel V) : FreeStep a l b ↔
    ∃ (ns : List SourceName) (a' b' : Extended V),
      Structural a (Named.restrictNames ns (.embed a')) ∧
      Structural b (Named.restrictNames ns (.embed b')) ∧ Extended.FreeStep a' l b' ∧
      ∀ n ∈ ns, n ∉ l.nameSupport := by
  constructor
  · exact fun h => h.prenex
  · rintro ⟨ns,a',b',ha,hb,hr,hn⟩
    exact .congr ha ((FreeStep.embed hr).restrictNames ns hn) hb.symm

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
