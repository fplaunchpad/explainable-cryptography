import ExplainableCrypto.Helios.Symbolic.SourceCoordinatedInternal

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- Outputs in current shared coordinates identify the original publication and
retain those coordinates on the entire enlarged target domain. -/
theorem source_coordinated_output_next (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (e k : Nat ≃ Nat) (phase : Process.Phase) (hr : phase.inRange extra)
    {a : Named (Fin phase.handles)} {b : Named (Option (Fin phase.handles))}
    (ha : Named.JointOpening a (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k))
    {c : Nat} (h : Named.BoundOutput a c b) :
    ∃ handle m next, Publication ns swap left right extra phase handle m next ∧
      Process.Step ns swap left right extra phase (.output handle) next ∧ c = k ch.broadcast ∧
      CoordinatedPhaseOpening ns swap left right extra ch e k next (b.rename Extended.outputHandle) := by
  obtain ⟨m,q,hq⟩ := ha.output_step h
  have hqi : Agent.Visible (residual ns swap left right extra ch phase)
      (.output (k.symm c) (m.mapNames e.symm)) (q.mapNames e.symm k.symm) := by
    simpa only [Agent.mapNames_inverse,Agent.PayloadEvent.mapNames,sourceState] using hq.mapNames e.symm k.symm
  have hpublic : k.symm c ∉ ch.privateChannels := by
    have hh := ha.bound_channel_public ((sourceState ns swap left right extra ch phase).mapNames e k) h
    exact (channel_public_mapNames_iff (k.symm c) ch.privateChannels k).mp (by simpa only [Equiv.apply_symm_apply] using hh)
  obtain ⟨handle,next,hpub,hchan,_⟩ := (residual_public_output_iff ns swap left right extra ch phase hr _ _ _ hpublic).mp hqi
  have hlabel : c = k ch.broadcast := by simpa only [Equiv.apply_symm_apply] using congrArg k hchan
  have hmapped : Agent.Visible ((residual ns swap left right extra ch phase).mapNames e k)
      (.output c m) ((residual ns swap left right extra ch next).mapNames e k) := by
    simpa only [Agent.PayloadEvent.mapNames,← hlabel,
      show (m.mapNames e.symm).mapNames e = m from Term.mapNames_inverse m e.symm] using (hpub.visible ch).mapNames e k
  have ht := ha.output_target h (fun n s hs => Agent.output_determinism_mapNames _
    (residual_visible_output_deterministic ns swap left right extra ch hc phase) e k _ _ _ _ _ hs hmapped)
  have ht' : Named.JointOpening (b.rename Extended.outputHandle)
      (Named.mappedState ch.privateChannels
        (⟨(sourceView ns swap left right phase).extend (m.mapNames e.symm),residual ns swap left right extra ch next⟩ :
          ScopedState ns.restricted (phase.handles+1)) e k) := by
    simpa only [Named.mappedState,ScopedState.mapNames,Frame.mapNames_extend,sourceState,
      show (m.mapNames e.symm).mapNames e = m from Term.mapNames_inverse m e.symm] using ht
  exact ⟨handle,m.mapNames e.symm,next,hpub,hpub.stage,hlabel,hpub.next_handles,
    ht'.cast_mapped_state hpub.next_handles (hpub.target_state ch)⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
