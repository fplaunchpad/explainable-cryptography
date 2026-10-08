import ExplainableCrypto.Helios.Symbolic.SourceRawInputMatching

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- Every actual publication has a same-channel fresh output from the raw
partner. Both full successor presentations use the same extended handle domain
and private coordinates, retaining all public observations. -/
theorem source_reachable_bound_match (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (e k : Nat ≃ Nat) (phase : Process.Phase) (hr : Process.Reachable ns swap left right extra phase)
    {a d : Named (Fin phase.handles)} {b : Named (Option (Fin phase.handles))}
    (ha : Named.JointOpening a (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k))
    (hd : Named.JointOpening d (Named.mappedState ch.privateChannels (sourceState ns swap' left right extra ch phase) e k))
    (hpa : a.RepresentsFrame (ch.privateChannels.image k) ((sourceView ns swap left right phase).mapNames e))
    (hpd : d.RepresentsFrame (ch.privateChannels.image k) ((sourceView ns swap' left right phase).mapNames e))
    {c : Nat} (h : Named.BoundOutput a c b) :
    ∃ (next : Process.Phase) (hh : phase.handles+1 = next.handles)
      (t : Named (Option (Fin phase.handles))),
      Named.BoundOutput d c t ∧
      Process.Reachable ns swap left right extra next ∧
      Process.Reachable ns swap' left right extra next ∧
      Named.JointOpening ((b.rename Extended.outputHandle).rename (Fin.cast hh))
        (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch next) e k) ∧
      Named.JointOpening ((t.rename Extended.outputHandle).rename (Fin.cast hh))
        (Named.mappedState ch.privateChannels (sourceState ns swap' left right extra ch next) e k) ∧
      ((b.rename Extended.outputHandle).rename (Fin.cast hh)).RepresentsFrame (ch.privateChannels.image k)
        ((sourceView ns swap left right next).mapNames e) ∧
      ((t.rename Extended.outputHandle).rename (Fin.cast hh)).RepresentsFrame (ch.privateChannels.image k)
        ((sourceView ns swap' left right next).mapNames e) ∧
      Named.StaticEq ((b.rename Extended.outputHandle).rename (Fin.cast hh))
        ((t.rename Extended.outputHandle).rename (Fin.cast hh)) := by
  obtain ⟨handle,m,next,_,hs,hchannel,hb⟩ := source_coordinated_output_next ns swap left right extra ch hc
    e k phase hr.wellFormed.inRange ha h
  have hother := hs.swap hf swap' hr.wellFormed.publicHistory hr.wellFormed.pendingPublic
  obtain ⟨m',hpub⟩ := stage_output_publication hother
  have hv := (hpub.visible ch).mapNames e k
  simp only [Agent.PayloadEvent.mapNames,← hchannel] at hv
  have hchan : c ∉ ch.privateChannels.image k := by
    rw [hchannel]
    exact (channel_public_mapNames_iff _ _ k).mpr (Channels.broadcast_public hc)
  obtain ⟨t,ht⟩ := hd.bound_available hchan hv.hasOutput
  have hj := hd.output_target ht (fun v q hq =>
    (Agent.output_determinism_mapNames _
      (residual_visible_output_deterministic ns swap' left right extra ch hc phase) e k)
      _ _ _ _ _ hq hv)
  have hj' : Named.JointOpening (t.rename Extended.outputHandle)
      (Named.mappedState ch.privateChannels
        (⟨(sourceView ns swap' left right phase).extend m',residual ns swap' left right extra ch next⟩ :
          ScopedState ns.restricted (phase.handles+1)) e k) := by
    simpa only [Named.mappedState,ScopedState.mapNames,sourceState,Frame.mapNames_extend] using hj
  have htphase : CoordinatedPhaseOpening ns swap' left right extra ch e k next
      (t.rename Extended.outputHandle) :=
    ⟨hpub.next_handles,hj'.cast_mapped_state hpub.next_handles (hpub.target_state ch)⟩
  obtain ⟨policy,channels,φ,hpb⟩ := h.exists_frame_presentation hpa
  obtain ⟨hh,hb,hpb⟩ := hb.presented hpb
  obtain ⟨policy',channels',ψ,hpt⟩ := ht.exists_frame_presentation hpd
  obtain ⟨hh',htjoint,hpt⟩ := htphase.presented hpt
  have hreach : Process.Reachable ns swap left right extra next := hr.tail ⟨_,hs⟩
  refine ⟨next,hh,t,ht,hreach,hreach.swap hf swap',hb,htjoint,hpb,hpt,?_⟩
  have he := reachable_source_view_staticEq hf (hreach.swap hf false)
  have hsview : (sourceView ns swap left right next).StaticEq (sourceView ns swap' left right next) := by
    cases swap <;> cases swap'
    · exact .refl _
    · exact he
    · exact he.symm
    · exact .refl _
  exact Named.StaticEq.of_presentations hpb hpt (hsview.mapNames e)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
