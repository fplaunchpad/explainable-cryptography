import ExplainableCrypto.Helios.Symbolic.SourceCanonicalOpeningInvariant

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

/-- A deterministic target modulo full evaluation equivalence is invariant
under a coherent permutation of all base and channel names. -/
theorem Agent.tau_target_mapNames (p q : Agent Empty)
    (hd : ∀ r, Agent.Tau p r → Agent.EvalEq r q) (e k : Nat ≃ Nat) :
    ∀ r, Agent.Tau (p.mapNames e k) r → Agent.EvalEq r (q.mapNames e k) := by
  intro r hr
  have ht : Agent.Tau p (r.mapNames e.symm k.symm) := by
    simpa only [Agent.mapNames_inverse] using hr.mapNames e.symm k.symm
  have he := (hd _ ht).mapNames e k
  simpa only [show (r.mapNames e.symm k.symm).mapNames e k = r from
    Agent.mapNames_inverse r e.symm k.symm] using he

namespace Named
variable {restricted : Finset Nat} {handles : Nat}

/-- An actual internal action from the invariant has a genuine Tau in the
original canonical coordinates. Source Structural presentation is unnecessary. -/
theorem HasCanonicalOpening.tau {a b : Named (Fin handles)}
    {φ : Frame restricted handles} {p : Agent Empty} (ha : HasCanonicalOpening a φ p)
    (h : Reduction a b) : ∃ q, Agent.Tau p q := by
  obtain ⟨needed,hh⟩ := h.opening_step
  obtain ⟨ns,c,e,k,ho,hf,he⟩ := ha.fresh needed
  obtain ⟨c',d,_,_,hr,hc,_,_,_⟩ := hh ∅ ns c ho
    (by intro n hn hm
        exact hf n hn (Finset.mem_union_left _ (by simpa only [Finset.empty_union] using hm)))
  have hs := hc.symm.trans he
  have hp : c'.Realizes (φ.mapNames e).value (p.mapNames e k) := (hs _ _).mpr (by
    rw [Extended.frameProcess_mapNames]
    exact Extended.frameProcess_realizes _ _)
  obtain ⟨q,hq,_⟩ := hr.realizes _ hp
  exact ⟨q.mapNames e.symm k.symm,by simpa only [Agent.mapNames_inverse] using hq.mapNames e.symm k.symm⟩

/-- Internal actions preserve the full canonical-opening invariant whenever
the canonical successor is deterministic modulo full evaluation equivalence.
The output witness can be refreshed for another arbitrary source action. -/
theorem HasCanonicalOpening.internal {a b : Named (Fin handles)}
    {φ : Frame restricted handles} {p q : Agent Empty} (ha : HasCanonicalOpening a φ p)
    (h : Reduction a b) (hd : ∀ r, Agent.Tau p r → Agent.EvalEq r q) :
    HasCanonicalOpening b φ q := by
  obtain ⟨needed,hh⟩ := h.opening_step
  obtain ⟨ns,c,e,k,ho,hf,he⟩ := ha.fresh (b.freeNames ∪ needed)
  obtain ⟨c',d,ms,b',hr,hc,hb,hj,hg⟩ := hh b.freeNames ns c ho
    (fun n hn hm => hf n hn (Finset.mem_union_left _ hm))
  have hs : c'.SameRealizations (Extended.frameProcess (φ.mapNames e) (p.mapNames e k)) := by
    simpa only [Extended.frameProcess_mapNames] using hc.symm.trans he
  have ht := hr.sameRealizations_frame_target (φ.mapNames e) (p.mapNames e k) (q.mapNames e k)
    hs (Agent.tau_target_mapNames p q hd e k)
  refine ⟨ms,b',e,k,hb,fun n hn hm => hg n hn (Finset.mem_union_left _ hm),?_⟩
  simpa only [Extended.frameProcess_mapNames] using hj.symm.trans ht

end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
