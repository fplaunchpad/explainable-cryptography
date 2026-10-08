import ExplainableCrypto.Helios.Symbolic.SourcePairedCanonicalPermutations
import ExplainableCrypto.Helios.Symbolic.SourceJointOpeningPolicy
import ExplainableCrypto.Helios.Symbolic.SourceCanonicalOpeningInternal

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {restricted hidden : Finset Nat} {handles : Nat}

/-- Consume an actual raw internal action without losing the canonical name
restrictions. Both full target classes use the same endpoint permutations and
both actual target openings avoid the union of the target free-name sets. -/
theorem JointOpening.internal {a b : Named (Fin handles)}
    {φ : Frame restricted handles} {p q : Agent Empty}
    (ha : JointOpening a (restrictedState hidden ⟨φ,p⟩)) (h : Reduction a b)
    (hd : ∀ r, Agent.Tau p r → Agent.EvalEq r q) :
    JointOpening b (restrictedState hidden ⟨φ,q⟩) := by
  let targetNames := b.freeNames ∪ (restrictedState hidden (⟨φ,q⟩ : ScopedState restricted handles)).freeNames
  let endpoints := (Extended.frameProcess φ p).nameSupport ∪ (Extended.frameProcess φ q).nameSupport
  obtain ⟨needed,hh⟩ := h.opening_step
  obtain ⟨ns,c,ks,t,ho,hcan,hf,hg,he,_⟩ := ha.fresh ((targetNames ∪ needed) ∪ endpoints)
  obtain ⟨c',d,ms,b',hr,hc,hb,hj,hf'⟩ := hh targetNames ns c ho
    (fun n hn hm => hf n hn (Finset.mem_union_left _ (Finset.mem_union_left _ hm)))
  obtain ⟨e,k,ht,hnext⟩ := hcan.prefix_permutations_pair (restrictionNames hidden restricted)
    (Extended.frameProcess φ p) (Extended.frameProcess φ q)
    (fun n hn hm => hg n hn (Finset.mem_union_left _ (Finset.mem_union_right _ hm)))
  have hs : c'.SameRealizations (Extended.frameProcess (φ.mapNames e) (p.mapNames e k)) := by
    rw [ht,Extended.frameProcess_mapNames] at he
    exact hc.symm.trans he
  have ht' := hr.sameRealizations_frame_target (φ.mapNames e) (p.mapNames e k) (q.mapNames e k)
    hs (Agent.tau_target_mapNames p q hd e k)
  have hb' : b'.SameRealizations ((Extended.frameProcess φ q).mapNames e k) := by
    simpa only [Extended.frameProcess_mapNames] using hj.symm.trans ht'
  refine ⟨ms,b',ks,_,hb,hnext,?_,?_,hb',(φ.mapNames e).value,q.mapNames e k,(hb' _ _).mpr ?_⟩
  · intro n hn hm
    exact hf' n hn (Finset.mem_union_left _ hm)
  · intro n hn hm
    exact hg n hn (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hm)))
  · rw [Extended.frameProcess_mapNames]
    exact Extended.frameProcess_realizes (φ.mapNames e) (q.mapNames e k)

/-- The actual internal step has a canonical Tau in the original coordinates. -/
theorem JointOpening.tau {a b : Named (Fin handles)}
    {φ : Frame restricted handles} {p : Agent Empty}
    (ha : JointOpening a (restrictedState hidden ⟨φ,p⟩)) (h : Reduction a b) :
    ∃ q, Agent.Tau p q := (ha.hasCanonicalOpening ⟨φ,p⟩).tau h

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
