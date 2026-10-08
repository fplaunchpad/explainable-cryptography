import ExplainableCrypto.Helios.Symbolic.SourceCoordinatedPhases

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- A public recipe under the current coordinates reflects to a public
original recipe and an actual check phase. The raw target keeps the same
coordinates, complete frame/body and restrictions at that phase. -/
theorem source_coordinated_public_input_next (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (e k : Nat ≃ Nat) (phase : Process.Phase) (hr : phase.inRange extra)
    {a b : Named (Fin phase.handles)}
    (ha : Named.JointOpening a (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k))
    {c : Nat} {r : Recipe phase.handles} (h : Named.FreeStep a (.input c r) b)
    (hp : r.Public (ns.restricted.image e)) :
    ∃ (rs : List (Recipe 3)) (s : Recipe 3), phase = .input rs ∧ HEq (r.mapNames e.symm) s ∧
      s.Public ns.restricted ∧ c = k (ch.voter (rs.length+2)) ∧
      Process.Step ns swap left right extra phase (.input (rs.length+2) s) (.check rs s) ∧
      CoordinatedPhaseOpening ns swap left right extra ch e k (.check rs s) b := by
  obtain ⟨q,hq⟩ := ha.public_input_step h hp
  have hqi := hq.input_inverse_frame e k
  have hpublic : (r.mapNames e.symm).Public ns.restricted := by
    simpa only [names_image_inverse] using (Term.public_mapNames_iff r e.symm (ns.restricted.image e)).mpr hp
  have hchan : k.symm c ∉ ch.privateChannels := by
    have hh := ha.free_channel_public ((sourceState ns swap left right extra ch phase).mapNames e k) h
    exact (channel_public_mapNames_iff (k.symm c) ch.privateChannels k).mp (by simpa only [Equiv.apply_symm_apply,Extended.FreeLabel.channel] using hh)
  have hsc : ScopedStep ch.privateChannels ns.restricted (sourceState ns swap left right extra ch phase)
      (.input (k.symm c) (r.mapNames e.symm)) ⟨sourceView ns swap left right phase,q.mapNames e.symm k.symm⟩ :=
    .input _ _ _ hchan hpublic hqi
  obtain ⟨_,rs,hphase,hchannel,s,he,_,_⟩ :=
    (source_scoped_input_iff ns swap left right extra ch hc phase hr _ _ _).mp hsc
  subst phase
  have hes : r.mapNames e.symm = s := eq_of_heq he
  subst s
  have hv := residual_visible_input ns swap left right extra ch rs (r.mapNames e.symm) hr
  rw [← hchannel] at hv
  have hmapped := hv.input_forward_frame e k
  have ht := ha.public_input_target h hp (fun t ht =>
    Agent.input_determinism_mapNames (residual ns swap left right extra ch (.input rs))
      (residual_visible_input_deterministic ns swap left right extra ch hc (.input rs)) e k
      _ _ t _ ht hmapped)
  have hlabel : c = k (ch.voter (rs.length+2)) := by
    simpa only [Equiv.apply_symm_apply] using congrArg k hchannel
  exact ⟨rs,r.mapNames e.symm,rfl,HEq.rfl,hpublic,hlabel,.input hr hpublic,
    CoordinatedPhaseOpening.of_joint ht⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
