import ExplainableCrypto.Helios.Symbolic.SourceCanonicalOpeningInvariant

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named

/-- Two actual name-scoped processes admit jointly fresh openings with the
same complete realization class and at least one realization. Freshness is
against both free-name sets; the two allocation lists need not be equal. -/
def JointOpening (a d : Named V) : Prop :=
  ∃ ns b ms c,
    Opens a NameAssignment.literal ns b ∧ Opens d NameAssignment.literal ms c ∧
    (∀ n ∈ ns, n ∉ a.freeNames ∪ d.freeNames) ∧
    (∀ n ∈ ms, n ∉ a.freeNames ∪ d.freeNames) ∧
    b.SameRealizations c ∧ ∃ env p, b.Realizes env p

variable {V : Type}

theorem JointOpening.embed {a d : Extended V} (h : a.SameRealizations d)
    {env : V → Ground} {p : Agent Empty} (hr : a.Realizes env p) :
    JointOpening (.embed a) (.embed d) := by
  refine ⟨[],a,[],d,?_,?_,by simp,by simp,h,env,p,hr⟩
  · simpa only [show NameAssignment.literal.base = id from rfl,
      show NameAssignment.literal.channel = id from rfl,Extended.mapNames_id] using Opens.embed a NameAssignment.literal
  · simpa only [show NameAssignment.literal.base = id from rfl,
      show NameAssignment.literal.channel = id from rfl,Extended.mapNames_id] using Opens.embed d NameAssignment.literal

/-- A full canonical state has a nonempty realization class in every chosen
fresh opening. This supplies a concrete positive control for the relation. -/
theorem restrictedState_jointOpening {restricted hidden : Finset Nat} {handles : Nat}
    (s : ScopedState restricted handles) :
    JointOpening (restrictedState hidden s) (restrictedState hidden s) := by
  obtain ⟨ns,b,e,k,ho,_,hf,_,_,hr,_⟩ := exists_fresh_canonical_opening s
    ((restrictedState hidden s).freeNames ∪ (restrictedState hidden s).freeNames)
  exact ⟨ns,b,ns,b,ho,ho,hf,hf,.refl _,_,_,hr⟩

/-- One jointly fresh pair can be refreshed by the same two value permutations.
This retains the relation of private allocations across the two processes. -/
theorem JointOpening.fresh {a d : Named V} (h : JointOpening a d)
    (avoid : Finset SourceName) :
    ∃ ns b ms c,
      Opens a NameAssignment.literal ns b ∧ Opens d NameAssignment.literal ms c ∧
      (∀ n ∈ ns, n ∉ avoid ∪ (a.freeNames ∪ d.freeNames)) ∧
      (∀ n ∈ ms, n ∉ avoid ∪ (a.freeNames ∪ d.freeNames)) ∧
      b.SameRealizations c ∧ ∃ env p, b.Realizes env p := by
  obtain ⟨ns,b,ms,c,ha,hd,hf,hg,he,env,p,hr⟩ := h
  obtain ⟨ls,e,k,_,_,hl,_,_,hm,hfix⟩ := exists_common_fresh_prefix (ns++ms)
    (.embed b) (.embed c) (avoid ∪ (a.freeNames ∪ d.freeNames))
  have fix : ∀ n ∈ a.freeNames ∪ d.freeNames, n.map e k = n := by
    intro n hn
    apply hfix n (Finset.mem_union_right _ hn)
    intro hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hf n hh hn
    · exact hg n hh hn
  have fresh : ∀ n ∈ (ns++ms).map (SourceName.map e k),
      n ∉ avoid ∪ (a.freeNames ∪ d.freeNames) := by
    intro n hn
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hn
    exact hl _ (hm u hu)
  refine ⟨_,_,_,_,ha.mapValues_literal e k (fun n hn => fix n (Finset.mem_union_left _ hn)),
    hd.mapValues_literal e k (fun n hn => fix n (Finset.mem_union_right _ hn)),?_,?_,
    he.mapNames e k,_,_,hr.mapNames e k⟩
  · intro n hn
    exact fresh n (by simpa only [List.map_append,List.mem_append] using Or.inl hn)
  · intro n hn
    exact fresh n (by simpa only [List.map_append,List.mem_append] using Or.inr hn)

theorem JointOpening.symm {a d : Named V} (h : JointOpening a d) : JointOpening d a := by
  obtain ⟨ns,b,ms,c,ha,hd,hf,hg,he,env,p,hr⟩ := h
  refine ⟨ms,c,ns,b,hd,ha,?_,?_,he.symm,env,p,(he env p).mp hr⟩
  · simpa only [Finset.union_comm] using hg
  · simpa only [Finset.union_comm] using hf

/-- Every source structural change on either side retains the joint relation;
no equality of allocation lists or literal private binder spellings is assumed. -/
theorem JointOpening.structural_right {a d d' : Named V} (h : JointOpening a d)
    (hs : Structural d d') : JointOpening a d' := by
  obtain ⟨ns,b,ms,c,ha,hd,hf,hg,he,env,p,hr⟩ := h.fresh (a.freeNames ∪ d'.freeNames)
  have hf' : ∀ n ∈ ns, n ∉ a.freeNames ∪ d'.freeNames :=
    fun n hn hh => hf n hn (Finset.mem_union_left _ hh)
  obtain ⟨ls,t,ht,hj,hc⟩ := hs.transport_opening _ ms c (a.freeNames ∪ d'.freeNames) hd
    (fun n hn hh => hg n hn (Finset.mem_union_left _ hh))
  exact ⟨ns,b,ls,t,ha,ht,hf',hj,he.trans hc,env,p,hr⟩

theorem JointOpening.structural_left {a a' d : Named V} (h : JointOpening a d)
    (hs : Structural a a') : JointOpening a' d := (h.symm.structural_right hs).symm

theorem Structural.jointOpening {restricted hidden : Finset Nat} {handles : Nat}
    (s : ScopedState restricted handles) {a : Named (Fin handles)}
    (h : Structural (restrictedState hidden s) a) :
    JointOpening a (restrictedState hidden s) := (restrictedState_jointOpening s).structural_left h

/-- Nonvacuity is explicit: both actual processes share a complete interpretation. -/
theorem JointOpening.interprets {a d : Named V} (h : JointOpening a d) :
    ∃ env p, a.Interprets NameAssignment.literal env p ∧ d.Interprets NameAssignment.literal env p := by
  obtain ⟨ns,b,ms,c,ha,hd,_,_,he,env,p,hr⟩ := h
  exact ⟨env,p,ha.interprets env hr,hd.interprets env ((he env p).mp hr)⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
