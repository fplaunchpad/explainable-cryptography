import ExplainableCrypto.Helios.Symbolic.SourceJointPublicInput

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {restricted hidden : Finset Nat} {handles : Nat}

/-- Actual bound output has a complete canonical message and continuation at
the same literal public channel, not merely an inverse-permuted channel. -/
theorem JointOpening.output_step {a : Named (Fin handles)} {b : Named (Option (Fin handles))}
    {φ : Frame restricted handles} {p : Agent Empty}
    (ha : JointOpening a (restrictedState hidden ⟨φ,p⟩)) {c : Nat} (h : BoundOutput a c b) :
    ∃ m q, Agent.Visible p (.output c m) q := by
  let F := Extended.frameProcess φ p
  let S := F.nameSupport ∪ {SourceName.channel c}
  obtain ⟨ns,d,ks,t,ho,hcan,_,hg,he,_⟩ := ha.fresh S
  obtain ⟨d',u,_,_,hr,hh,_,_,_⟩ := h.opening_step ∅ ho (by simp)
  obtain ⟨e,k,ht,_,hfix⟩ := hcan.prefix_permutations_fixed_pair (restrictionNames hidden restricted) F F S
    Finset.subset_union_left Finset.subset_union_left
    (fun n hn hm => hg n hn (Finset.mem_union_left _ hm))
  have hc : c ∉ hidden := ha.bound_channel_public ⟨φ,p⟩ h
  have hkc : k c = c := SourceName.channel.inj (hfix (.channel c)
    (Finset.mem_union_right _ (Finset.mem_singleton_self _))
    (fun hn => hc ((channel_mem_restrictionNames c hidden restricted).mp hn)))
  have hs : d'.SameRealizations (Extended.frameProcess (φ.mapNames e) (p.mapNames e k)) := by
    rw [ht,Extended.frameProcess_mapNames] at he
    exact hh.symm.trans he
  obtain ⟨m,q,hq,_⟩ := hr.realizes (φ.mapNames e).value ((hs _ _).mpr (Extended.frameProcess_realizes _ _))
  have hk : k.symm c = c := by simpa only [hkc] using k.symm_apply_apply c
  exact ⟨m.mapNames e.symm,q.mapNames e.symm k.symm,by
    simpa only [Agent.mapNames_inverse,Agent.PayloadEvent.mapNames,hk] using hq.mapNames e.symm k.symm⟩

/-- Every old handle, the full new handle and the actual restrictions survive
bound output. The paired canonical endpoint has the new variable domain. -/
theorem JointOpening.output_target {a : Named (Fin handles)} {b : Named (Option (Fin handles))}
    {φ : Frame restricted handles} {p q : Agent Empty} {m : Ground}
    (ha : JointOpening a (restrictedState hidden ⟨φ,p⟩)) {c : Nat} (h : BoundOutput a c b)
    (hd : ∀ n s, Agent.Visible p (.output c n) s → EqE n m ∧ Agent.EvalEq s q) :
    JointOpening (b.rename Extended.outputHandle) (restrictedState hidden ⟨φ.extend m,q⟩) := by
  let targetNames := (b.rename Extended.outputHandle).freeNames ∪
    (restrictedState hidden (⟨φ.extend m,q⟩ : ScopedState restricted (handles+1))).freeNames
  let F := Extended.frameProcess φ p
  let G := Extended.frameProcess (φ.extend m) q
  let S := (F.nameSupport ∪ G.nameSupport) ∪ {SourceName.channel c}
  obtain ⟨ns,d,ks,t,ho,hcan,hf,hg,he,_⟩ := ha.fresh (targetNames ∪ S)
  obtain ⟨d',u,ms,b',hr,hh,hb,hj,hbFresh⟩ := h.opening_step targetNames ho
    (fun n hn hm => hf n hn (Finset.mem_union_left _ (Finset.mem_union_left _ hm)))
  obtain ⟨e,k,ht,hnext,hfix⟩ := hcan.prefix_permutations_fixed_pair (restrictionNames hidden restricted) F G S
    (fun n hn => Finset.mem_union_left _ (Finset.mem_union_left _ hn))
    (fun n hn => Finset.mem_union_left _ (Finset.mem_union_right _ hn))
    (fun n hn hm => hg n hn (Finset.mem_union_left _ (Finset.mem_union_right _ hm)))
  have hc : c ∉ hidden := ha.bound_channel_public ⟨φ,p⟩ h
  have hkc : k c = c := SourceName.channel.inj (hfix (.channel c)
    (Finset.mem_union_right _ (Finset.mem_singleton_self _))
    (fun hn => hc ((channel_mem_restrictionNames c hidden restricted).mp hn)))
  have hs : d'.SameRealizations (Extended.frameProcess (φ.mapNames e) (p.mapNames e k)) := by
    rw [ht,Extended.frameProcess_mapNames] at he
    exact hh.symm.trans he
  have hdet : ∀ n s, Agent.Visible (p.mapNames e k) (.output c n) s →
      EqE n (m.mapNames e) ∧ Agent.EvalEq s (q.mapNames e k) := by
    intro n s hs'
    have hk : k.symm c = c := by simpa only [hkc] using k.symm_apply_apply c
    have hi : Agent.Visible p (.output c (n.mapNames e.symm)) (s.mapNames e.symm k.symm) := by
      simpa only [Agent.mapNames_inverse,Agent.PayloadEvent.mapNames,hk] using hs'.mapNames e.symm k.symm
    obtain ⟨hm,hq⟩ := hd _ _ hi
    constructor
    · simpa only [show (n.mapNames e.symm).mapNames e = n from Term.mapNames_inverse n e.symm] using hm.mapNames e
    · simpa only [show (s.mapNames e.symm k.symm).mapNames e k = s from Agent.mapNames_inverse s e.symm k.symm]
        using hq.mapNames e k
  have htarget : (b'.rename Extended.outputHandle).SameRealizations (G.mapNames e k) := by
    simpa only [G,Extended.frameProcess_mapNames,Frame.mapNames_extend] using (hj.rename Extended.outputHandle).symm.trans
      (hr.sameRealizations_target (φ.mapNames e) (p.mapNames e k) (q.mapNames e k) (m.mapNames e) hs hdet)
  refine ⟨ms,_,ks,_,hb.rename _,hnext,hbFresh,?_,htarget,((φ.extend m).mapNames e).value,
    q.mapNames e k,(htarget _ _).mpr ?_⟩
  · intro n hn hm
    exact hg n hn (Finset.mem_union_left _ (Finset.mem_union_left _ hm))
  · rw [Extended.frameProcess_mapNames]
    exact Extended.frameProcess_realizes _ _

theorem JointOpening.bound_output {a : Named (Fin handles)} {b : Named (Option (Fin handles))}
    {φ : Frame restricted handles} {p : Agent Empty}
    (ha : JointOpening a (restrictedState hidden ⟨φ,p⟩)) {c : Nat} (h : BoundOutput a c b)
    (hd : ∀ c m q n s, Agent.Visible p (.output c m) q → Agent.Visible p (.output c n) s →
      EqE m n ∧ Agent.EvalEq q s) :
    ∃ m q, Agent.Visible p (.output c m) q ∧
      JointOpening (b.rename Extended.outputHandle) (restrictedState hidden ⟨φ.extend m,q⟩) := by
  obtain ⟨m,q,hq⟩ := ha.output_step h
  exact ⟨m,q,hq,ha.output_target h (fun n s hs => hd _ _ _ _ _ hs hq)⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
