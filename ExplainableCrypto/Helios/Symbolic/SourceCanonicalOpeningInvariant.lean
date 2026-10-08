import ExplainableCrypto.Helios.Symbolic.SourceOpeningValuePermutations

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named

/-- A full canonical interpretation class carried by an externally fresh
opening. Both directions quantify all environments and complete process bodies.
The coordinate permutations are witnesses, not source actions or equations. -/
def HasCanonicalOpening {restricted : Finset Nat} {handles : Nat}
    (a : Named (Fin handles)) (φ : Frame restricted handles) (p : Agent Empty) : Prop :=
  ∃ (ns : List SourceName) (b : Extended (Fin handles)) (e k : Nat ≃ Nat),
    Opens a NameAssignment.literal ns b ∧ (∀ n ∈ ns, n ∉ a.freeNames) ∧
    b.SameRealizations ((Extended.frameProcess φ p).mapNames e k)

variable {restricted hidden : Finset Nat} {handles : Nat}

theorem HasCanonicalOpening.fresh {a : Named (Fin handles)}
    {φ : Frame restricted handles} {p : Agent Empty} (h : HasCanonicalOpening a φ p)
    (avoid : Finset SourceName) :
    ∃ (ns : List SourceName) (b : Extended (Fin handles)) (e k : Nat ≃ Nat),
      Opens a NameAssignment.literal ns b ∧ (∀ n ∈ ns, n ∉ avoid ∪ a.freeNames) ∧
      b.SameRealizations ((Extended.frameProcess φ p).mapNames e k) := by
  obtain ⟨ns,b,e,k,ho,hf,he⟩ := h
  obtain ⟨j,l,hb,hg,_⟩ := ho.refresh hf avoid
  refine ⟨_,_,e.trans j,k.trans l,hb,hg,?_⟩
  simpa only [Extended.mapNames_comp,Equiv.coe_trans] using he.mapNames j l

theorem HasCanonicalOpening.structural {a b : Named (Fin handles)}
    {φ : Frame restricted handles} {p : Agent Empty} (h : HasCanonicalOpening a φ p)
    (hs : Structural a b) : HasCanonicalOpening b φ p := by
  obtain ⟨ns,c,e,k,ho,hf,he⟩ := h.fresh b.freeNames
  obtain ⟨ms,d,hd,hg,hj⟩ := hs.transport_opening _ ns c b.freeNames ho
    (fun n hn hm => hf n hn (Finset.mem_union_left _ hm))
  exact ⟨ms,d,e,k,hd,hg,hj.symm.trans he⟩

theorem restrictedState_hasCanonicalOpening (s : ScopedState restricted handles) :
    HasCanonicalOpening (restrictedState hidden s) s.frame s.body := by
  obtain ⟨ns,b,e,k,ho,_,hf,_,he,_,_⟩ := exists_fresh_canonical_opening s
    (restrictedState hidden s).freeNames
  refine ⟨ns,b,e,k,ho,hf,?_⟩
  rw [Extended.frameProcess_mapNames,← he]
  exact .refl _

theorem Structural.hasCanonicalOpening (s : ScopedState restricted handles)
    {a : Named (Fin handles)} (h : Structural (restrictedState hidden s) a) :
    HasCanonicalOpening a s.frame s.body :=
  (restrictedState_hasCanonicalOpening s).structural h

/-- The invariant is nonvacuous and supplies the entire raw interpretation in
one coherent frame/body coordinate system. -/
theorem HasCanonicalOpening.interprets {a : Named (Fin handles)}
    {φ : Frame restricted handles} {p : Agent Empty} (h : HasCanonicalOpening a φ p) :
    ∃ e k : Nat ≃ Nat,
      a.Interprets NameAssignment.literal (φ.mapNames e).value (p.mapNames e k) := by
  obtain ⟨ns,b,e,k,ho,_,he⟩ := h
  refine ⟨e,k,ho.interprets _ ((he _ _).mpr ?_)⟩
  rw [Extended.frameProcess_mapNames]
  exact Extended.frameProcess_realizes _ _

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
