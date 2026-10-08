import ExplainableCrypto.Helios.Symbolic.SourceOpeningFaithfulness

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type} {restricted hidden : Finset Nat} {handles : Nat}

theorem allNames_subset_restrictNames (bound : List SourceName) (a : Named V) :
    a.allNames ⊆ (restrictNames bound a).allNames := by
  induction bound with
  | nil => exact Finset.Subset.refl _
  | cons n ns ih => exact ih.trans (Finset.subset_insert _ _)

/-- A fresh opening of a canonical full state is exactly a permutation of its
entire frame/body, not merely an existential collapsed interpretation. The
permutation witnesses are constructed from the recorded allocation. -/
theorem Opens.canonical_permutations (s : ScopedState restricted handles)
    {ns : List SourceName} {b : Extended (Fin handles)}
    (h : Opens (restrictedState hidden s) NameAssignment.literal ns b)
    (hf : ∀ n ∈ ns, n ∉ (Extended.frameProcess s.frame s.body).nameSupport) :
    ∃ e k : Nat ≃ Nat,
      b = Extended.frameProcess (s.frame.mapNames e) (s.body.mapNames e k) ∧
      b.Realizes (s.frame.mapNames e).value (s.body.mapNames e k) ∧
      s.body.ReadyGuardsRetract e e.symm := by
  obtain ⟨e,k,hb⟩ := h.prefix_permutations (restrictionNames hidden restricted)
    (Extended.frameProcess s.frame s.body) hf
  rw [Extended.frameProcess_mapNames] at hb
  exact ⟨e,k,hb,hb ▸ Extended.frameProcess_realizes (s.frame.mapNames e) (s.body.mapNames e k),
    Agent.ReadyGuardsRetract.of_inverse s.body e⟩

theorem exists_fresh_canonical_opening (s : ScopedState restricted handles)
    (avoid : Finset SourceName) :
    ∃ (ns : List SourceName) (b : Extended (Fin handles)) (e k : Nat ≃ Nat),
      Opens (restrictedState hidden s) NameAssignment.literal ns b ∧ ns.Nodup ∧
      (∀ n ∈ ns, n ∉ avoid) ∧
      Structural (restrictedState hidden s) (restrictNames ns (.embed b)) ∧
      b = Extended.frameProcess (s.frame.mapNames e) (s.body.mapNames e k) ∧
      b.Realizes (s.frame.mapNames e).value (s.body.mapNames e k) ∧
      s.body.ReadyGuardsRetract e e.symm := by
  obtain ⟨ns,b,hb,hd,hf,hs⟩ := exists_fresh_opening_structural (restrictedState hidden s) avoid
  have hf' : ∀ n ∈ ns, n ∉ (Extended.frameProcess s.frame s.body).nameSupport := by
    intro n hn hm
    exact hf n hn (Finset.mem_union_right _
      (allNames_subset_restrictNames (restrictionNames hidden restricted) (.embed (Extended.frameProcess s.frame s.body)) hm))
  obtain ⟨e,k,he,hr,hg⟩ := hb.canonical_permutations s hf'
  exact ⟨ns,b,e,k,hb,hd,fun n hn hm => hf n hn (Finset.mem_union_left _ hm),hs,he,hr,hg⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
