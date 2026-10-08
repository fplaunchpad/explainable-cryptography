import ExplainableCrypto.Helios.Symbolic.SourceOutputRealizationClosure

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V W : Type}

/-- A pure prefix opens any second body with the same actual allocation and
assignment, even when bound output changes its variable type. The assignment
is fixed outside the original name prefix. -/
theorem Opens.prefix_pair_assignment (bound : List SourceName) (a : Extended V) (c : Extended W)
    (ρ : NameAssignment) {ns : List SourceName} {b : Extended V}
    (h : Opens (restrictNames bound (.embed a)) ρ ns b) :
    ∃ τ : NameAssignment, b = a.mapNames τ.base τ.channel ∧
      Opens (restrictNames bound (.embed c)) ρ ns (c.mapNames τ.base τ.channel) ∧
      ∀ n, n ∉ bound → τ n = ρ n := by
  induction bound generalizing ρ ns with
  | nil => cases h; exact ⟨ρ,rfl,.embed c ρ,fun _ _ => rfl⟩
  | cons n bound ih =>
    cases h with
    | newName _ v h hn =>
      obtain ⟨τ,hb,hc,hfix⟩ := ih (Function.update ρ n v) h
      refine ⟨τ,hb,.newName n v hc hn,?_⟩
      intro m hm
      have hmn : m ≠ n := fun he => hm (he ▸ List.mem_cons_self)
      rw [hfix m (fun hmem => hm (List.mem_cons_of_mem _ hmem)),Function.update_of_ne hmn]

theorem Opens.prefix_freeStep (bound : List SourceName) {a b : Extended V} {l : Extended.FreeLabel V}
    (hr : Extended.FreeStep a l b) (ρ : NameAssignment) {ns : List SourceName} {a' : Extended V}
    (ho : Opens (restrictNames bound (.embed a)) ρ ns a')
    (hn : ∀ n ∈ bound, n ∉ l.nameSupport) :
    ∃ b', Opens (restrictNames bound (.embed b)) ρ ns b' ∧
      Extended.FreeStep a' (l.mapNames ρ.base ρ.channel) b' := by
  obtain ⟨τ,he,hb,hfix⟩ := ho.prefix_pair_assignment bound a b ρ
  have hl : l.mapNames τ.base τ.channel = l.mapNames ρ.base ρ.channel :=
    l.mapAssignments_congr τ ρ (fun n hm => hfix n (fun hns => hn n hns hm))
  refine ⟨_,hb,?_⟩
  rw [he,← hl]
  exact hr.mapNames τ.base τ.channel

theorem Opens.prefix_boundOutput (bound : List SourceName) {a : Extended V}
    {b : Extended (Option V)} {c : Nat} (hr : Extended.BoundOutput a c b)
    (ρ : NameAssignment) {ns : List SourceName} {a' : Extended V}
    (ho : Opens (restrictNames bound (.embed a)) ρ ns a')
    (hn : ∀ n ∈ bound, n ≠ SourceName.channel c) :
    ∃ b', Opens (restrictNames bound (.embed b)) ρ ns b' ∧
      Extended.BoundOutput a' (ρ.channel c) b' := by
  obtain ⟨τ,he,hb,hfix⟩ := ho.prefix_pair_assignment bound a b ρ
  have hc : τ.channel c = ρ.channel c := hfix (.channel c) (fun hns => hn _ hns rfl)
  refine ⟨_,hb,?_⟩
  rw [he,← hc]
  exact hr.mapNames τ.base τ.channel

/-- Free actions preserve the literal full public label through paired
openings; arbitrary extra finite avoidance and both full comparisons remain. -/
theorem FreeStep.opening_binder_step {a b : Named V} {l : Extended.FreeLabel V}
    (h : FreeStep a l b) (avoid : Finset SourceName) {ns : List SourceName} {a' : Extended V}
    (ho : Opens a NameAssignment.literal ns a') (hf : ∀ n ∈ ns, n ∉ avoid) :
    ∃ (c d : Extended V) (ms : List SourceName) (b' : Extended V),
      Extended.FreeStep c l d ∧ a'.BinderStructural c ∧ Opens b NameAssignment.literal ms b' ∧
      d.BinderStructural b' ∧ (∀ n ∈ ms, n ∉ avoid) := by
  obtain ⟨bound,c,d,hc,hd,hr,hn⟩ := h.prenex
  obtain ⟨ks,c',hc',hg,he⟩ := hc.transport_binder_opening _ ns a' avoid ho hf
  obtain ⟨d',hd',hr'⟩ := hc'.prefix_freeStep bound hr NameAssignment.literal hn
  have hl : l.mapNames NameAssignment.literal.base NameAssignment.literal.channel = l := by
    change l.mapNames id id = l
    cases l <;> simp only [Extended.FreeLabel.mapNames,Term.mapNames_id]
    all_goals rfl
  rw [hl] at hr'
  obtain ⟨ms,b',hb',hh,hj⟩ := hd.symm.transport_binder_opening _ ks d' avoid hd' hg
  exact ⟨c',d',ms,b',hr',he,hb',hj,hh⟩

/-- Bound output retains one actual opened action and the complete fresh
variable target, rather than only an emitted-value interpretation witness. -/
theorem BoundOutput.opening_binder_step {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) (avoid : Finset SourceName) {ns : List SourceName} {a' : Extended V}
    (ho : Opens a NameAssignment.literal ns a') (hf : ∀ n ∈ ns, n ∉ avoid) :
    ∃ (d : Extended V) (t : Extended (Option V)) (ms : List SourceName) (b' : Extended (Option V)),
      Extended.BoundOutput d c t ∧ a'.BinderStructural d ∧ Opens b NameAssignment.literal ms b' ∧
      t.BinderStructural b' ∧ (∀ n ∈ ms, n ∉ avoid) := by
  obtain ⟨bound,d,t,hd,ht,hr,hn⟩ := h.prenex
  obtain ⟨ks,d',hd',hg,he⟩ := hd.transport_binder_opening _ ns a' avoid ho hf
  obtain ⟨t',ht',hr'⟩ := hd'.prefix_boundOutput bound hr NameAssignment.literal hn
  obtain ⟨ms,b',hb',hh,hj⟩ := ht.symm.transport_binder_opening _ ks t' avoid ht' hg
  exact ⟨d',t',ms,b',hr',he,hb',hj,hh⟩

/-- Realization compatibility follows from the retained structural paths. -/
theorem FreeStep.opening_step {a b : Named V} {l : Extended.FreeLabel V}
    (h : FreeStep a l b) (avoid : Finset SourceName) {ns : List SourceName} {a' : Extended V}
    (ho : Opens a NameAssignment.literal ns a') (hf : ∀ n ∈ ns, n ∉ avoid) :
    ∃ (c d : Extended V) (ms : List SourceName) (b' : Extended V),
      Extended.FreeStep c l d ∧ a'.SameRealizations c ∧ Opens b NameAssignment.literal ms b' ∧
      d.SameRealizations b' ∧ (∀ n ∈ ms, n ∉ avoid) := by
  obtain ⟨c,d,ms,b',hr,hs,hb,ht,hfresh⟩ := h.opening_binder_step avoid ho hf
  exact ⟨c,d,ms,b',hr,hs.sameRealizations,hb,ht.sameRealizations,hfresh⟩

/-- Realization compatibility follows from the retained structural paths. -/
theorem BoundOutput.opening_step {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) (avoid : Finset SourceName) {ns : List SourceName} {a' : Extended V}
    (ho : Opens a NameAssignment.literal ns a') (hf : ∀ n ∈ ns, n ∉ avoid) :
    ∃ (d : Extended V) (t : Extended (Option V)) (ms : List SourceName) (b' : Extended (Option V)),
      Extended.BoundOutput d c t ∧ a'.SameRealizations d ∧ Opens b NameAssignment.literal ms b' ∧
      t.SameRealizations b' ∧ (∀ n ∈ ms, n ∉ avoid) := by
  obtain ⟨c,d,ms,b',hr,hs,hb,ht,hfresh⟩ := h.opening_binder_step avoid ho hf
  exact ⟨c,d,ms,b',hr,hs.sameRealizations,hb,ht.sameRealizations,hfresh⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
