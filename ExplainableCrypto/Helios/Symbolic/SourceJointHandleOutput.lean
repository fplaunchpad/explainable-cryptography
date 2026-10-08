import ExplainableCrypto.Helios.Symbolic.SourceJointPublicInput
import ExplainableCrypto.Helios.Symbolic.SourceHandleOutputClosure

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {restricted hidden : Finset Nat} {handles : Nat}

/-- An actual existing-handle output retains the literal public channel and
the full value of its old handle under jointly fresh canonical openings. -/
theorem JointOpening.handle_output_step {a b : Named (Fin handles)}
    {φ : Frame restricted handles} {p : Agent Empty}
    (ha : JointOpening a (restrictedState hidden ⟨φ,p⟩)) {c : Nat} {x : Fin handles} (h : FreeStep a (.output c x) b) :
    ∃ m q, EqE (φ.value x) m ∧ Agent.Visible p (.output c m) q := by
  let F := Extended.frameProcess φ p
  let S := F.nameSupport ∪ {SourceName.channel c}
  obtain ⟨ns,d,ks,t,ho,hcan,_,hg,he,_⟩ := ha.fresh S
  obtain ⟨d',u,_,_,hr,hh,_,_,_⟩ := h.opening_step ∅ ho (by simp)
  obtain ⟨e,k,ht,_,hfix⟩ := hcan.prefix_permutations_fixed_pair (restrictionNames hidden restricted) F F S
    Finset.subset_union_left Finset.subset_union_left
    (fun n hn hm => hg n hn (Finset.mem_union_left _ hm))
  have hc : c ∉ hidden := ha.free_channel_public ⟨φ,p⟩ h
  have hkc : k c = c := SourceName.channel.inj (hfix (.channel c)
    (Finset.mem_union_right _ (Finset.mem_singleton_self _))
    (fun hn => hc ((channel_mem_restrictionNames c hidden restricted).mp hn)))
  have hs : d'.SameRealizations (Extended.frameProcess (φ.mapNames e) (p.mapNames e k)) := by
    rw [ht,Extended.frameProcess_mapNames] at he
    exact hh.symm.trans he
  obtain ⟨m,q,hm,hq,_⟩ := hr.output_realizes (φ.mapNames e).value ((hs _ _).mpr (Extended.frameProcess_realizes _ _))
  have hk : k.symm c = c := by simpa only [hkc] using k.symm_apply_apply c
  refine ⟨m.mapNames e.symm,q.mapNames e.symm k.symm,?_,?_⟩
  · simpa only [Frame.mapNames,Term.mapNames_inverse] using hm.mapNames e.symm
  · simpa only [Agent.mapNames_inverse,Agent.PayloadEvent.mapNames,hk] using hq.mapNames e.symm k.symm

/-- A free output retains every old handle, the old domain and actual name
restrictions. Determinism concerns outputs equal to the labelled handle. -/
theorem JointOpening.handle_output_target {a b : Named (Fin handles)}
    {φ : Frame restricted handles} {p q : Agent Empty}
    (ha : JointOpening a (restrictedState hidden ⟨φ,p⟩)) {c : Nat} {x : Fin handles} (h : FreeStep a (.output c x) b)
    (hd : ∀ n s, EqE (φ.value x) n → Agent.Visible p (.output c n) s → Agent.EvalEq s q) :
    JointOpening b (restrictedState hidden ⟨φ,q⟩) := by
  let targetNames := b.freeNames ∪
    (restrictedState hidden (⟨φ,q⟩ : ScopedState restricted handles)).freeNames
  let F := Extended.frameProcess φ p
  let G := Extended.frameProcess φ q
  let S := (F.nameSupport ∪ G.nameSupport) ∪ {SourceName.channel c}
  obtain ⟨ns,d,ks,t,ho,hcan,hf,hg,he,_⟩ := ha.fresh (targetNames ∪ S)
  obtain ⟨d',u,ms,b',hr,hh,hb,hj,hbFresh⟩ := h.opening_step targetNames ho
    (fun n hn hm => hf n hn (Finset.mem_union_left _ (Finset.mem_union_left _ hm)))
  obtain ⟨e,k,ht,hnext,hfix⟩ := hcan.prefix_permutations_fixed_pair (restrictionNames hidden restricted) F G S
    (fun n hn => Finset.mem_union_left _ (Finset.mem_union_left _ hn))
    (fun n hn => Finset.mem_union_left _ (Finset.mem_union_right _ hn))
    (fun n hn hm => hg n hn (Finset.mem_union_left _ (Finset.mem_union_right _ hm)))
  have hc : c ∉ hidden := ha.free_channel_public ⟨φ,p⟩ h
  have hkc : k c = c := SourceName.channel.inj (hfix (.channel c)
    (Finset.mem_union_right _ (Finset.mem_singleton_self _))
    (fun hn => hc ((channel_mem_restrictionNames c hidden restricted).mp hn)))
  have hs : d'.SameRealizations (Extended.frameProcess (φ.mapNames e) (p.mapNames e k)) := by
    rw [ht,Extended.frameProcess_mapNames] at he
    exact hh.symm.trans he
  have hdet : ∀ n s, EqE ((φ.mapNames e).value x) n → Agent.Visible (p.mapNames e k) (.output c n) s →
      Agent.EvalEq s (q.mapNames e k) := by
    intro n s hn hs'
    have hk : k.symm c = c := by simpa only [hkc] using k.symm_apply_apply c
    have hi : Agent.Visible p (.output c (n.mapNames e.symm)) (s.mapNames e.symm k.symm) := by
      simpa only [Agent.mapNames_inverse,Agent.PayloadEvent.mapNames,hk] using hs'.mapNames e.symm k.symm
    have hv : EqE (φ.value x) (n.mapNames e.symm) := by
      simpa only [Frame.mapNames,Term.mapNames_inverse] using hn.mapNames e.symm
    simpa only [show (s.mapNames e.symm k.symm).mapNames e k = s from Agent.mapNames_inverse s e.symm k.symm]
      using (hd _ _ hv hi).mapNames e k
  have htarget : b'.SameRealizations (G.mapNames e k) := by
    simpa only [G,Extended.frameProcess_mapNames] using hj.symm.trans
      (hr.output_sameRealizations_target (φ.mapNames e) (p.mapNames e k) (q.mapNames e k) hs hdet)
  refine ⟨ms,_,ks,_,hb,hnext,hbFresh,?_,htarget,(φ.mapNames e).value,
    q.mapNames e k,(htarget _ _).mpr ?_⟩
  · intro n hn hm
    exact hg n hn (Finset.mem_union_left _ (Finset.mem_union_left _ hm))
  · rw [Extended.frameProcess_mapNames]
    exact Extended.frameProcess_realizes _ _

/-- A real handle-labelled output selects a canonical continuation and retains
the complete joint target. Global output determinism discharges the local premise. -/
theorem JointOpening.handle_output {a b : Named (Fin handles)}
    {φ : Frame restricted handles} {p : Agent Empty}
    (ha : JointOpening a (restrictedState hidden ⟨φ,p⟩))
    {c : Nat} {x : Fin handles} (h : FreeStep a (.output c x) b)
    (hd : ∀ c m q n s, Agent.Visible p (.output c m) q → Agent.Visible p (.output c n) s →
      EqE m n ∧ Agent.EvalEq q s) :
    ∃ m q, EqE (φ.value x) m ∧ Agent.Visible p (.output c m) q ∧
      JointOpening b (restrictedState hidden ⟨φ,q⟩) := by
  obtain ⟨m,q,hm,hq⟩ := ha.handle_output_step h
  exact ⟨m,q,hm,hq,ha.handle_output_target h (fun n s _ hs => (hd _ _ _ _ _ hs hq).2)⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
