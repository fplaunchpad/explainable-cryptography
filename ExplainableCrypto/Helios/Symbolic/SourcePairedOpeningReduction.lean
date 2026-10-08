import ExplainableCrypto.Helios.Symbolic.SourceRealizationTargetClosure

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- One allocation of a pure prefix opens both Extended endpoints with the
same faithful assignment. The paired target witness is constructed explicitly. -/
theorem Opens.prefix_faithful_pair (bound : List SourceName) (a c : Extended V)
    (ρ : NameAssignment) {ns : List SourceName} {b : Extended V}
    (h : Opens (restrictNames bound (.embed a)) ρ ns b) (S : Finset SourceName)
    (hi : ρ.FaithfulOn S)
    (hf : ∀ n ∈ ns, n ∉ S.image (SourceName.map ρ.base ρ.channel)) :
    ∃ τ : NameAssignment, b = a.mapNames τ.base τ.channel ∧ τ.FaithfulOn S ∧
      Opens (restrictNames bound (.embed c)) ρ ns (c.mapNames τ.base τ.channel) := by
  induction bound generalizing ρ ns with
  | nil =>
    cases h
    exact ⟨ρ,rfl,hi,.embed c ρ⟩
  | cons n bound ih =>
    cases h with
    | newName _ v h hn =>
      obtain ⟨τ,hb,ht,hc⟩ := ih (Function.update ρ n v) h
        (hi.update_fresh n v (hf _ List.mem_cons_self))
        (fun m hm => nameAssignment_fresh_update_image ρ S n v m
          (hf m (List.mem_cons_of_mem _ hm)) (fun he => hn (he ▸ hm)))
      exact ⟨τ,hb,ht,.newName n v hc hn⟩

/-- The actual reduced Extended endpoints can be opened together, retaining
one actual reduction and the complete chosen source body. -/
theorem Opens.prefix_reduction (bound : List SourceName) {a b : Extended V}
    (hr : Extended.Reduction a b) (ρ : NameAssignment) {ns : List SourceName}
    {a' : Extended V} (ho : Opens (restrictNames bound (.embed a)) ρ ns a')
    (hi : ρ.FaithfulOn (a.nameSupport ∪ b.nameSupport))
    (hf : ∀ n ∈ ns, n ∉ (a.nameSupport ∪ b.nameSupport).image
      (SourceName.map ρ.base ρ.channel)) :
    ∃ b', Opens (restrictNames bound (.embed b)) ρ ns b' ∧ Extended.Reduction a' b' := by
  obtain ⟨τ,he,ht,hb⟩ := ho.prefix_faithful_pair bound a b ρ _ hi hf
  exact ⟨_,hb,he ▸ ((Extended.reduction_mapAssignments_iff a b τ ht).mpr hr)⟩

/-- An actual Named action has a paired opened Extended action. Full source
and target realization comparisons surround that action, and any extra finite
avoidance is retained. Neither comparison is an assumed input witness. -/
theorem Reduction.opening_binder_step {a b : Named V} (h : Reduction a b) :
    ∃ needed : Finset SourceName,
      ∀ (avoid : Finset SourceName) (ns : List SourceName) (a' : Extended V),
        Opens a NameAssignment.literal ns a' → (∀ n ∈ ns, n ∉ avoid ∪ needed) →
        ∃ (c d : Extended V) (ms : List SourceName) (b' : Extended V),
          Extended.Reduction c d ∧ a'.BinderStructural c ∧
          Opens b NameAssignment.literal ms b' ∧ d.BinderStructural b' ∧
          (∀ n ∈ ms, n ∉ avoid ∪ needed) := by
  obtain ⟨bound,c,d,hc,hd,hr⟩ := h.prenex
  let needed := c.nameSupport ∪ d.nameSupport
  refine ⟨needed,?_⟩
  intro avoid ns a' ho hf
  obtain ⟨ks,c',hc',hg,he⟩ := hc.transport_binder_opening _ ns a' (avoid ∪ needed) ho hf
  have hmap : SourceName.map NameAssignment.literal.base NameAssignment.literal.channel = id := by
    funext n; cases n <;> rfl
  have hi : NameAssignment.literal.FaithfulOn needed := by
    intro x y hx hy hxy
    simpa only [hmap,id_eq] using hxy
  have hfg : ∀ n ∈ ks, n ∉ needed.image
      (SourceName.map NameAssignment.literal.base NameAssignment.literal.channel) := by
    simpa only [hmap,Finset.image_id] using
      (fun n hn hm => hg n hn (Finset.mem_union_right avoid hm))
  obtain ⟨d',hd',hr'⟩ := hc'.prefix_reduction bound hr NameAssignment.literal hi hfg
  obtain ⟨ms,b',hb',hh,hj⟩ := hd.symm.transport_binder_opening _ ks d' (avoid ∪ needed) hd' hg
  exact ⟨c',d',ms,b',hr',he,hb',hj,hh⟩

/-- Realization compatibility follows from the retained structural paths. -/
theorem Reduction.opening_step {a b : Named V} (h : Reduction a b) :
    ∃ needed : Finset SourceName,
      ∀ (avoid : Finset SourceName) (ns : List SourceName) (a' : Extended V),
        Opens a NameAssignment.literal ns a' → (∀ n ∈ ns, n ∉ avoid ∪ needed) →
        ∃ (c d : Extended V) (ms : List SourceName) (b' : Extended V),
          Extended.Reduction c d ∧ a'.SameRealizations c ∧
          Opens b NameAssignment.literal ms b' ∧ d.SameRealizations b' ∧
          (∀ n ∈ ms, n ∉ avoid ∪ needed) := by
  obtain ⟨needed,ht⟩ := h.opening_binder_step
  refine ⟨needed,?_⟩
  intro avoid ns a' ho hf
  obtain ⟨c,d,ms,b',hr,hs,hb,ht,hfresh⟩ := ht avoid ns a' ho hf
  exact ⟨c,d,ms,b',hr,hs.sameRealizations,hb,ht.sameRealizations,hfresh⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
