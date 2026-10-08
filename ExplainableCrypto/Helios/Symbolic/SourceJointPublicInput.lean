import ExplainableCrypto.Helios.Symbolic.SourcePairedOpeningObservations
import ExplainableCrypto.Helios.Symbolic.SourceJointOpeningPolicy
import ExplainableCrypto.Helios.Symbolic.SourceVisibleDeterminismPermutations

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {restricted hidden : Finset Nat} {handles : Nat}

/-- An actual input with a public recipe has its exact canonical input label.
The public channel follows from the joint relation and the actual source action. -/
theorem JointOpening.public_input_step {a b : Named (Fin handles)}
    {φ : Frame restricted handles} {p : Agent Empty}
    (ha : JointOpening a (restrictedState hidden ⟨φ,p⟩))
    {c : Nat} {r : Recipe handles} (h : FreeStep a (.input c r) b) (hp : r.Public restricted) :
    ∃ q, Agent.Visible p (.input c (φ.eval r)) q := by
  let F := Extended.frameProcess φ p
  let S := F.nameSupport ∪ (Extended.FreeLabel.input c r).nameSupport
  obtain ⟨ns,d,ks,t,ho,hcan,hf,hg,he,_⟩ := ha.fresh S
  obtain ⟨d',u,_,_,hr,hh,_,_,_⟩ := h.opening_step ∅ ho (by simp)
  obtain ⟨e,k,ht,_,hfix⟩ := hcan.prefix_permutations_fixed_pair (restrictionNames hidden restricted) F F S
    Finset.subset_union_left Finset.subset_union_left
    (fun n hn hm => hg n hn (Finset.mem_union_left _ hm))
  have hn := (input_restriction_fresh_iff c r).mpr ⟨ha.free_channel_public ⟨φ,p⟩ h,hp⟩
  obtain ⟨hkc,her⟩ := input_label_fixed (fun n hn' => hfix n (Finset.mem_union_right _ hn')
    (fun hb => hn n hb hn'))
  have hs : d'.SameRealizations (Extended.frameProcess (φ.mapNames e) (p.mapNames e k)) := by
    rw [ht,Extended.frameProcess_mapNames] at he
    exact hh.symm.trans he
  obtain ⟨q,hq,_⟩ := hr.input_realizes (φ.mapNames e).value ((hs _ _).mpr (Extended.frameProcess_realizes _ _))
  have hv : (r.subst (φ.mapNames e).value).mapNames e.symm = φ.eval r := by
    have heval := Frame.mapNames_eval φ r e
    rw [her] at heval
    change ((φ.mapNames e).eval r).mapNames e.symm = _
    rw [heval,Term.mapNames_inverse]
  have hk : k.symm c = c := by simpa only [hkc] using k.symm_apply_apply c
  exact ⟨q.mapNames e.symm k.symm,by
    simpa only [Agent.mapNames_inverse,Agent.PayloadEvent.mapNames,hv,hk] using hq.mapNames e.symm k.symm⟩

/-- Full joint target closure retains the exact public recipe and actual
canonical restrictions. Determinism is at that complete evaluated input. -/
theorem JointOpening.public_input_target {a b : Named (Fin handles)}
    {φ : Frame restricted handles} {p q : Agent Empty}
    (ha : JointOpening a (restrictedState hidden ⟨φ,p⟩))
    {c : Nat} {r : Recipe handles} (h : FreeStep a (.input c r) b) (hp : r.Public restricted)
    (hd : ∀ s, Agent.Visible p (.input c (φ.eval r)) s → Agent.EvalEq s q) :
    JointOpening b (restrictedState hidden ⟨φ,q⟩) := by
  let targetNames := b.freeNames ∪ (restrictedState hidden (⟨φ,q⟩ : ScopedState restricted handles)).freeNames
  let F := Extended.frameProcess φ p
  let G := Extended.frameProcess φ q
  let S := (F.nameSupport ∪ G.nameSupport) ∪ (Extended.FreeLabel.input c r).nameSupport
  obtain ⟨ns,d,ks,t,ho,hcan,hf,hg,he,_⟩ := ha.fresh (targetNames ∪ S)
  obtain ⟨d',u,ms,b',hr,hh,hb,hj,hbFresh⟩ := h.opening_step targetNames ho
    (fun n hn hm => hf n hn (Finset.mem_union_left _ (Finset.mem_union_left _ hm)))
  obtain ⟨e,k,ht,hnext,hfix⟩ := hcan.prefix_permutations_fixed_pair (restrictionNames hidden restricted) F G S
    (fun n hn => Finset.mem_union_left _ (Finset.mem_union_left _ hn))
    (fun n hn => Finset.mem_union_left _ (Finset.mem_union_right _ hn))
    (fun n hn hm => hg n hn (Finset.mem_union_left _ (Finset.mem_union_right _ hm)))
  have hn := (input_restriction_fresh_iff c r).mpr ⟨ha.free_channel_public ⟨φ,p⟩ h,hp⟩
  obtain ⟨hkc,her⟩ := input_label_fixed (fun n hn' => hfix n (Finset.mem_union_right _ hn')
    (fun hb => hn n hb hn'))
  have hs : d'.SameRealizations (Extended.frameProcess (φ.mapNames e) (p.mapNames e k)) := by
    rw [ht,Extended.frameProcess_mapNames] at he
    exact hh.symm.trans he
  have hdet : ∀ s, Agent.Visible (p.mapNames e k) (.input c ((φ.mapNames e).eval r)) s →
      Agent.EvalEq s (q.mapNames e k) := by
    intro s hs'
    have hv : ((φ.mapNames e).eval r).mapNames e.symm = φ.eval r := by
      have heval := Frame.mapNames_eval φ r e
      rw [her] at heval
      rw [heval,Term.mapNames_inverse]
    have hk : k.symm c = c := by simpa only [hkc] using k.symm_apply_apply c
    have hi : Agent.Visible p (.input c (φ.eval r)) (s.mapNames e.symm k.symm) := by
      simpa only [Agent.mapNames_inverse,Agent.PayloadEvent.mapNames,hv,hk] using hs'.mapNames e.symm k.symm
    simpa only [show (s.mapNames e.symm k.symm).mapNames e k = s from Agent.mapNames_inverse s e.symm k.symm]
      using (hd _ hi).mapNames e k
  have htarget : b'.SameRealizations (G.mapNames e k) := by
    simpa only [G,Extended.frameProcess_mapNames] using hj.symm.trans
      (hr.input_sameRealizations_target (φ.mapNames e) (p.mapNames e k) (q.mapNames e k) hs hdet)
  refine ⟨ms,b',ks,_,hb,hnext,hbFresh,?_,htarget,(φ.mapNames e).value,q.mapNames e k,(htarget _ _).mpr ?_⟩
  · intro n hn hm
    exact hg n hn (Finset.mem_union_left _ (Finset.mem_union_left _ hm))
  · rw [Extended.frameProcess_mapNames]
    exact Extended.frameProcess_realizes _ _

theorem JointOpening.public_input {a b : Named (Fin handles)}
    {φ : Frame restricted handles} {p : Agent Empty}
    (ha : JointOpening a (restrictedState hidden ⟨φ,p⟩))
    {c : Nat} {r : Recipe handles} (h : FreeStep a (.input c r) b) (hp : r.Public restricted)
    (hd : ∀ c m q s, Agent.Visible p (.input c m) q → Agent.Visible p (.input c m) s → Agent.EvalEq q s) :
    ∃ q, Agent.Visible p (.input c (φ.eval r)) q ∧ JointOpening b (restrictedState hidden ⟨φ,q⟩) := by
  obtain ⟨q,hq⟩ := ha.public_input_step h hp
  exact ⟨q,hq,ha.public_input_target h hp (fun s hs => hd _ _ _ _ hs hq)⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
