import ExplainableCrypto.Helios.Symbolic.SourceCaptureCopy

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {handles : Nat} {r hidden : Finset Nat}

/-- The full opened target has a ground structural presentation. The old
presentation and actual output supply all extraction, domain and model premises. -/
theorem BoundOutput.opened_frame_presentation {a : Named (Fin handles)}
    {b : Named (Option (Fin handles))} {c : Nat} {φ : Frame r handles}
    (h : BoundOutput a c b) (hp : a.RepresentsFrame hidden φ)
    {ρ : NameAssignment} {ns : List SourceName} {d : Extended (Option (Fin handles))}
    (ho : Opens b ρ ns d) :
    ∃ (f : Nat → Nat) (m : Ground),
      (d.frameOf.rename Extended.outputHandle).BinderStructural
        (Extended.activeFrame ((φ.mapNames f).extend m)) := by
  obtain ⟨f,hf⟩ := (hp.bound_reclose h).opening_presentation (.newVar ho)
  have hu : (Extended.newVar d.frameOf).UniqueDefinitions :=
    hf.named.uniqueDefinitions.mpr (Extended.activeFrame_wellFormed (φ.mapNames f)).1
  obtain ⟨m,hm⟩ := h.opened_capture_ground hp ho
  have hc := hm.ground_reclose hu.1 hu.2
  have hr := (hf.named.rename some (Option.some_injective _)).binder_of_embeds
  have hs := hc.trans (hr.parLeft (.active none (Extended.groundTerm m)))
  have ht := (hs.named.rename Extended.outputHandle Extended.outputHandle.injective).binder_of_embeds
  refine ⟨f,m,?_⟩
  have he : (((Extended.activeFrame (φ.mapNames f)).rename some).rename Extended.outputHandle) =
      (Extended.activeFrame (φ.mapNames f)).rename Fin.castSucc := by
    rw [Extended.rename_comp]
    congr 1
    funext i
    exact Extended.outputHandle_some i
  simp only [Extended.rename,Extended.groundTerm_subst,Extended.outputHandle_none,he] at ht
  exact ht.trans (by
    rw [Extended.activeFrame_extend]
    exact (Extended.Structural.comm _ _).binderStructural)

/-- Reclose the actual full name allocation, then use its exact base/channel
sets as an existential policy. This does not fix the old frame's policy. -/
theorem BoundOutput.exists_frame_presentation {a : Named (Fin handles)}
    {b : Named (Option (Fin handles))} {c : Nat} {φ : Frame r handles}
    (h : BoundOutput a c b) (hp : a.RepresentsFrame hidden φ) :
    ∃ (policy channels : Finset Nat) (ψ : Frame policy (handles+1)),
      (b.rename Extended.outputHandle).RepresentsFrame channels ψ := by
  classical
  obtain ⟨ns,d,ho,_,_,hb⟩ := exists_fresh_opening_structural b ∅
  obtain ⟨f,m,hd⟩ := h.opened_frame_presentation hp ho
  let policy := ns.toFinset.preimage SourceName.base (fun _ _ _ _ he => SourceName.base.inj he)
  let channels := ns.toFinset.preimage SourceName.channel (fun _ _ _ _ he => SourceName.channel.inj he)
  let ψ := ((φ.mapNames f).extend m).withPolicy policy
  have hpolicy (x : Nat) : x ∈ policy ↔ SourceName.base x ∈ ns :=
    Finset.mem_preimage.trans List.mem_toFinset
  have hchannels (x : Nat) : x ∈ channels ↔ SourceName.channel x ∈ ns :=
    Finset.mem_preimage.trans List.mem_toFinset
  have hnames : ns.toFinset = (restrictionNames channels policy).toFinset := by
    ext u
    cases u <;> simp [restrictionNames,hpolicy,hchannels]
  have hs := (hb.frameOf.rename Extended.outputHandle Extended.outputHandle.injective)
  simp only [frameOf_restrictNames,frameOf,restrictNames_rename,rename,← frameOf_rename] at hs
  have ht := hd.named.restrictNames ns
  have hn := Structural.restrictNames_of_toFinset_eq ns (restrictionNames channels policy) hnames
    (.embed (Extended.activeFrame ((φ.mapNames f).extend m)))
  exact ⟨policy,channels,ψ,hs.trans (ht.trans hn)⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
