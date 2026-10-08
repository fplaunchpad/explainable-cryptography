import ExplainableCrypto.Helios.Symbolic.SourceLocalCodePrefix

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended

private theorem code_prefix_internal_available (n : Nat) {handles : Nat}
    (f : Extended (LocalVars n (Fin handles))) (p : Agent (LocalVars n (Fin handles)))
    (hf : f.FrameForest) {φ : Frame ∅ handles}
    (hp : (closeVars n (.par f (.plain p))).frameOf.BinderStructural (activeFrame φ))
    {env : Fin handles → Ground} {before after : Agent Empty}
    (ha : (closeVars n (.par f (.plain p))).Realizes env before)
    (hτ : Agent.Tau before after) :
    ∃ b, Named.Reduction (.embed (closeVars n (.par f (.plain p)))) b := by
  induction n generalizing handles with
  | zero =>
    have hp' : (Extended.par f (.plain .nil)).BinderStructural (activeFrame φ) := by
      change (Extended.par f.frameOf (.plain .nil)).BinderStructural (activeFrame φ) at hp
      rw [hf.frameOf] at hp
      exact hp
    have hframe := (Structural.zero f).binderStructural.symm.trans hp'
    have he : p.subst (fun i => (groundTerm (φ.value i) : Term (Fin handles))) = groundAgent (p.subst φ.value) := by
      exact (Agent.subst_subst p φ.value Empty.elim).symm
    have hn : (Extended.par f (.plain p)).BinderStructural (frameProcess φ (p.subst φ.value)) := by
      have h := (hframe.parLeft (.plain p)).trans (activeFrame_apply φ p).binderStructural
      simpa only [frameProcess,he] using h
    have hb := (frameProcess_realizes_iff φ (p.subst φ.value) env before).mp
      ((hn.sameRealizations env before).mp ha)
    obtain ⟨q,hq,_⟩ := hb.2.symm.tau_transport hτ
    exact ⟨_,Named.Reduction.congr hn.named
      (.embed (.parRight (activeFrame φ) (tau_ground_derivable (Fin handles) hq))) (.refl _)⟩
  | succ n ih =>
    let a := closeVars n (.par f (.plain p))
    obtain ⟨ψ,hψ⟩ := hp.open_local_frame
    obtain ⟨v,hv⟩ := ha
    let renamedF := f.rename (localMap n outputHandle)
    let renamedP := p.subst (fun v => .var (localMap n outputHandle v))
    have hclose : a.rename outputHandle = closeVars n (.par renamedF (.plain renamedP)) :=
      closeVars_rename n (.par f (.plain p)) outputHandle
    have hpf : (closeVars n (.par renamedF (.plain renamedP))).frameOf.BinderStructural (activeFrame ψ) := by
      rw [← frameOf_rename] at hψ
      exact (congrArg (fun t => t.frameOf.BinderStructural (activeFrame ψ)) hclose).mp hψ
    have hv' : (a.rename outputHandle).Realizes
        (fun i => extendEnv env v (outputHandle.symm i)) before := by
      apply (realizes_rename a outputHandle _ _).mpr
      convert hv using 1 <;> first | rfl | simp only [Equiv.symm_apply_apply]
    have hr : (closeVars n (.par renamedF (.plain renamedP))).Realizes
        (fun i => extendEnv env v (outputHandle.symm i)) before := by
      exact (congrArg (fun t => t.Realizes
        (fun i => extendEnv env v (outputHandle.symm i)) before) hclose).mp hv'
    obtain ⟨b,hb⟩ := ih renamedF renamedP (hf.rename _) hpf hr
    have hb' : Named.Reduction (.embed (a.rename outputHandle)) b := by
      exact (congrArg (fun t => Named.Reduction (.embed t) b) hclose).mpr hb
    have hback := hb'.rename_equiv outputHandle.symm
    have hident : (a.rename outputHandle).rename outputHandle.symm = a := by
      rw [rename_comp]
      have he : (outputHandle.symm : Fin (handles+1) → Option (Fin handles)) ∘ outputHandle = id :=
        funext outputHandle.symm_apply_apply
      rw [he,rename_id]
    simp only [Named.rename,hident] at hback
    exact ⟨_,Named.Reduction.congr (Named.Structural.embedVar a) (.newVar hback) (.refl _)⟩

/-- Actual frame presentation supplies enough source structure to realize any
interpreted internal step, including grounding a ready conditional. Prefix and
local-frame witnesses are derived from the original process, not assumed. -/
theorem internal_available_of_presentation {handles : Nat} {a : Extended (Fin handles)}
    {φ : Frame ∅ handles} (hp : a.frameOf.BinderStructural (activeFrame φ))
    {env : Fin handles → Ground} {p q : Agent Empty} (ha : a.Realizes env p)
    (hτ : Agent.Tau p q) : ∃ b, Named.Reduction (.embed a) b := by
  obtain ⟨n,f,s,hf,hs⟩ := exists_local_code_prefix a
  have hframe := hs.frameOf.binderStructural.symm.trans hp
  obtain ⟨b,hb⟩ := code_prefix_internal_available n f s hf hframe ((hs.realizes env p).mp ha) hτ
  exact ⟨b,.congr (.embed hs) hb (.refl _)⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {restricted hidden : Finset Nat} {handles : Nat}

/-- The actual full current presentation and joint source interpretation derive
an original internal action. No ground-guard, local-program, availability or
normalization premise remains at the interface. -/
theorem JointOpening.internal_available {a : Named (Fin handles)}
    {φ : Frame restricted handles} {p q : Agent Empty}
    (ha : JointOpening a (restrictedState hidden ⟨φ,p⟩))
    (hp : a.RepresentsFrame hidden φ) (hτ : Agent.Tau p q) : ∃ b, Reduction a b := by
  let F := Extended.frameProcess φ p
  obtain ⟨ns,d,ms,t,ho,hcan,hf,hg,he,_⟩ := ha.fresh (a.allNames ∪ F.nameSupport)
  obtain ⟨e,k,ht,_,_⟩ := hcan.canonical_permutations (⟨φ,p⟩ : ScopedState restricted handles)
    (fun n hn hm => hg n hn (Finset.mem_union_left _ (Finset.mem_union_right _ hm)))
  have hd : d.Realizes (φ.mapNames e).value (p.mapNames e k) := by
    apply (he _ _).mpr
    rw [ht]
    exact Extended.frameProcess_realizes _ _
  obtain ⟨g,hp'⟩ := hp.opening_presentation ho
  have hground : d.frameOf.BinderStructural (Extended.activeFrame ((φ.mapNames g).withPolicy ∅)) := hp'
  obtain ⟨b,hb⟩ := Extended.internal_available_of_presentation hground hd (hτ.mapNames e k)
  have hs := ho.structural_literal (fun n hn hm => hf n hn
    (Finset.mem_union_left _ (Finset.mem_union_left _ hm)))
  exact ⟨_,.congr hs (hb.restrictNames ns) (.refl _)⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
