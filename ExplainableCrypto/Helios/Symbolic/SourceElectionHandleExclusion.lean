import ExplainableCrypto.Helios.Symbolic.SourcePublicationSeparation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- Every raw representative jointly related to a reached election in current
coordinates excludes old-handle free output. No normalization assumption is
needed, and the exclusion quantifies over all literal channels and targets. -/
theorem source_coordinated_no_handle_output (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (e k : Nat ≃ Nat) (phase : Process.Phase)
    (hr : Process.Reachable ns swap left right extra phase)
    {a : Named (Fin phase.handles)}
    (ha : Named.JointOpening a (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k))
    (c : Nat) (x : Fin phase.handles) (b : Named (Fin phase.handles)) :
    ¬ Named.FreeStep a (.output c x) b := by
  intro h
  obtain ⟨m,q,hm,hq⟩ := ha.handle_output_step h
  have hv : EqE ((sourceView ns swap left right phase).value x) (m.mapNames e.symm) := by
    simpa only [sourceState,ScopedState.mapNames,Frame.mapNames,Term.mapNames_inverse] using hm.mapNames e.symm
  have hqi : Agent.Visible (residual ns swap left right extra ch phase)
      (.output (k.symm c) (m.mapNames e.symm)) (q.mapNames e.symm k.symm) := by
    simpa only [Agent.mapNames_inverse,Agent.PayloadEvent.mapNames,sourceState] using hq.mapNames e.symm k.symm
  have hpublic : k.symm c ∉ ch.privateChannels := by
    have hh := ha.free_channel_public ((sourceState ns swap left right extra ch phase).mapNames e k) h
    exact (channel_public_mapNames_iff (k.symm c) ch.privateChannels k).mp
      (by simpa only [Extended.FreeLabel.channel,Equiv.apply_symm_apply] using hh)
  obtain ⟨handle,next,hpub,_,_⟩ := (residual_public_output_iff ns swap left right extra ch phase
    hr.wellFormed.inRange _ _ _ hpublic).mp hqi
  exact hpub.old_handle_distinct hf hr x hv

/-- Identity coordinates give the same all-target exclusion for the original
literal source state. -/
theorem source_joint_no_handle_output (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (phase : Process.Phase) (hr : Process.Reachable ns swap left right extra phase)
    {a : Named (Fin phase.handles)}
    (ha : Named.JointOpening a (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch phase)))
    (c : Nat) (x : Fin phase.handles) (b : Named (Fin phase.handles)) :
    ¬ Named.FreeStep a (.output c x) b :=
  source_coordinated_no_handle_output ns hf swap left right extra ch (Equiv.refl Nat) (Equiv.refl Nat)
    phase hr (by simpa only [Named.mappedState_identity] using ha) c x b

/-- The maintained phase invariant inherits the exclusion even when its raw
handle type is related to the phase domain by an explicit equality. -/
theorem CoordinatedPhaseOpening.no_handle_output {ns : Names n} (hf : ns.Fresh)
    {swap : Bool} {left right : CandidateSubstitution n Empty} {extra handles : Nat}
    {ch : Channels} {e k : Nat ≃ Nat} {phase : Process.Phase}
    {a : Named (Fin handles)} (ha : CoordinatedPhaseOpening ns swap left right extra ch e k phase a)
    (hr : Process.Reachable ns swap left right extra phase)
    (c : Nat) (x : Fin handles) (b : Named (Fin handles)) :
    ¬ Named.FreeStep a (.output c x) b := by
  obtain ⟨hh,ha⟩ := ha
  cases hh
  simp only [show Fin.cast (Eq.refl phase.handles) = id from rfl,Named.rename_id] at ha
  exact source_coordinated_no_handle_output ns hf swap left right extra ch e k phase hr ha c x b

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
