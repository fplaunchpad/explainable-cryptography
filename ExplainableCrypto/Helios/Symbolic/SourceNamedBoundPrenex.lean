import ExplainableCrypto.Helios.Symbolic.SourceBoundPairedPrenex

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- One Extended bound output witnesses every current Named bound output.
The channel and common name prefix are retained; the target has precisely the
extra Option variable required by the original source rule. -/
theorem BoundOutput.prenex {a : Named V} {b : Named (Option V)} {c : Nat} (h : BoundOutput a c b) :
    ∃ (ns : List SourceName) (a' : Extended V) (b' : Extended (Option V)),
      Structural a (Named.restrictNames ns (.embed a')) ∧
      Structural b (Named.restrictNames ns (.embed b')) ∧ Extended.BoundOutput a' c b' ∧
      ∀ n ∈ ns, n ≠ SourceName.channel c := by
  induction h with
  | embed h => exact ⟨[],_,_,.refl _,.refl _,h,by simp⟩
  | openAtom h =>
    obtain ⟨ns,a',b',ha,hb,hr,hn⟩ := h.prenex
    refine ⟨ns,.newVar a',b',?_,hb,.openAtom hr,?_⟩
    · exact (Structural.newVar ha).trans ((Structural.var_restrictNames _ ns).trans
        ((Structural.embedVar a').symm.restrictNames ns))
    · simpa only [Extended.FreeLabel.nameSupport,Finset.mem_singleton] using hn
  | scopeName n hf h ih =>
    obtain ⟨ns,a',b',ha,hb,hr,hn⟩ := ih
    refine ⟨n::ns,a',b',.newName n ha,.newName n hb,hr,?_⟩
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hf
    · exact hn m hm
  | scopeVar h ih =>
    obtain ⟨ns,a',b',ha,hb,hr,hn⟩ := ih
    have hb' := hb.rename Extended.swapBinders Extended.swapBinders_involutive.injective
    rw [restrictNames_rename] at hb'
    refine ⟨ns,.newVar a',.newVar (b'.rename Extended.swapBinders),?_,?_,.scope hr,hn⟩
    · exact (Structural.newVar ha).trans ((Structural.var_restrictNames _ ns).trans
        ((Structural.embedVar a').symm.restrictNames ns))
    · exact (Structural.newVar hb').trans ((Structural.var_restrictNames _ ns).trans
        ((Structural.embedVar (b'.rename Extended.swapBinders)).symm.restrictNames ns))
  | parLeft d h ih =>
    obtain ⟨ns,a',b',ha,hb,hr,hn⟩ := ih
    obtain ⟨ns',e,k,d',ha',hb',hn',hfix⟩ := bound_parallel_prenex_pair ns a' b' d {SourceName.channel _}
      (by simpa only [Finset.mem_singleton] using hn)
    have hc := SourceName.channel.inj (hfix (.channel _) (Finset.mem_singleton_self _))
    have hr' := hr.mapNames e k
    rw [hc] at hr'
    refine ⟨ns',_,_,(Structural.parLeft d ha).trans ha',
      (Structural.parLeft (d.rename some) hb).trans hb',.parLeft d' hr',?_⟩
    simpa only [Finset.mem_singleton] using hn'
  | parRight d h ih =>
    obtain ⟨ns,a',b',ha,hb,hr,hn⟩ := ih
    obtain ⟨ns',e,k,d',ha',hb',hn',hfix⟩ := bound_parallel_prenex_pair ns a' b' d {SourceName.channel _}
      (by simpa only [Finset.mem_singleton] using hn)
    have hc := SourceName.channel.inj (hfix (.channel _) (Finset.mem_singleton_self _))
    have hr' := hr.mapNames e k
    rw [hc] at hr'
    refine ⟨ns',_,_,(Structural.comm _ _).trans ((Structural.parLeft d ha).trans ha'),
      (Structural.comm _ _).trans ((Structural.parLeft (d.rename some) hb).trans hb'),.parLeft d' hr',?_⟩
    simpa only [Finset.mem_singleton] using hn'
  | congr hs h ht ih =>
    obtain ⟨ns,a',b',ha,hb,hr,hn⟩ := ih
    exact ⟨ns,a',b',hs.trans ha,ht.symm.trans hb,hr,hn⟩

theorem boundOutput_iff_prenex (a : Named V) (b : Named (Option V)) (c : Nat) : BoundOutput a c b ↔
    ∃ (ns : List SourceName) (a' : Extended V) (b' : Extended (Option V)),
      Structural a (restrictNames ns (.embed a')) ∧
      Structural b (restrictNames ns (.embed b')) ∧ Extended.BoundOutput a' c b' ∧
      ∀ n ∈ ns, n ≠ SourceName.channel c := by
  constructor
  · exact fun h => h.prenex
  · rintro ⟨ns,a',b',ha,hb,hr,hn⟩
    exact .congr ha ((BoundOutput.embed hr).restrictNames ns hn) hb.symm

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
