import ExplainableCrypto.Helios.Symbolic.SourceJointFreshInput
import ExplainableCrypto.Helios.Symbolic.SourceElectionJointInvariant
import ExplainableCrypto.Helios.Symbolic.SourceElectionVisibleInvariant

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- Election determinism discharges joint bound-output closure, retaining the
literal public channel, complete fresh handle and canonical restriction policy. -/
theorem source_joint_output_preserved (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (phase : Process.Phase) {a : Named (Fin phase.handles)} {b : Named (Option (Fin phase.handles))}
    (ha : Named.JointOpening a (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch phase)))
    {c : Nat} (h : Named.BoundOutput a c b) :
    ∃ m q, Agent.Visible (residual ns swap left right extra ch phase) (.output c m) q ∧
      Named.JointOpening (b.rename Extended.outputHandle)
        (Named.restrictedState ch.privateChannels ⟨(sourceView ns swap left right phase).extend m,q⟩) :=
  ha.bound_output h (residual_visible_output_deterministic ns swap left right extra ch hc phase)

theorem Publication.next_handles {ns : Names n} {swap : Bool}
    {left right : CandidateSubstitution n Empty} {extra handle : Nat}
    {phase next : Process.Phase} {m : Ground}
    (h : Publication ns swap left right extra phase handle m next) : phase.handles + 1 = next.handles := by
  cases h with
  | second => cases extra <;> rfl
  | _ => rfl

theorem Publication.target_state {ns : Names n} {swap : Bool}
    {left right : CandidateSubstitution n Empty} {extra handle : Nat}
    {phase next : Process.Phase} {m : Ground}
    (h : Publication ns swap left right extra phase handle m next) (ch : Channels) :
    HEq (⟨(sourceView ns swap left right phase).extend m,residual ns swap left right extra ch next⟩ :
      ScopedState ns.restricted (phase.handles+1)) (sourceState ns swap left right extra ch next) := by
  have hh := h.next_handles
  have hf := h.capture
  have lift (i j : Nat) (φ : Frame ns.restricted i) (ψ : Frame ns.restricted j)
      (he : i=j) (hf : HEq φ ψ) (body : Agent Empty) :
      HEq (⟨φ,body⟩ : ScopedState ns.restricted i) (⟨ψ,body⟩ : ScopedState ns.restricted j) := by
    subst j
    cases hf
    rfl
  exact lift _ _ _ _ hh hf _

/-- Full bound outputs identify an actual publication and next phase while
preserving the joint relation on the new handle domain. -/
theorem source_joint_output_next (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (phase : Process.Phase) (hr : phase.inRange extra)
    {a : Named (Fin phase.handles)} {b : Named (Option (Fin phase.handles))}
    (ha : Named.JointOpening a (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch phase)))
    {c : Nat} (h : Named.BoundOutput a c b) :
    ∃ handle m next, Publication ns swap left right extra phase handle m next ∧
      Process.Step ns swap left right extra phase (.output handle) next ∧ c = ch.broadcast ∧
      PhaseJointOpening ns swap left right extra ch next (b.rename Extended.outputHandle) := by
  obtain ⟨m,q,hq⟩ := ha.output_step h
  obtain ⟨handle,next,hpub,he,_⟩ := (residual_public_output_iff ns swap left right extra ch phase hr c m q
    (ha.bound_channel_public _ h)).mp hq
  subst c
  have ht := ha.output_target h (fun n s hs => residual_visible_output_deterministic ns swap left right extra ch hc phase
    _ n s m _ hs (hpub.visible ch))
  exact ⟨handle,m,next,hpub,hpub.stage,rfl,hpub.next_handles,
    ht.cast_state hpub.next_handles (hpub.target_state ch)⟩

/-- Arbitrary actual election inputs have one fresh policy in both vote worlds,
with unchanged raw labels, full old-frame equivalence and joint target closure.
Publicness is constructed, not assumed for the fixed original private names. -/
theorem source_joint_common_fresh_input (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (phase : Process.Phase) (hr : Process.Reachable ns swap left right extra phase)
    {a b d : Named (Fin phase.handles)}
    (ha : Named.JointOpening a (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch phase)))
    (hd : Named.JointOpening d (Named.restrictedState ch.privateChannels (sourceState ns swap' left right extra ch phase)))
    {c : Nat} {r : Recipe phase.handles} (h : Named.FreeStep a (.input c r) b) :
    ∃ (e k : Nat ≃ Nat) (q : Agent Empty),
      Named.Structural (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch phase))
        (Named.restrictedState (ch.privateChannels.image k) ((sourceState ns swap left right extra ch phase).mapNames e k)) ∧
      Named.Structural (Named.restrictedState ch.privateChannels (sourceState ns swap' left right extra ch phase))
        (Named.restrictedState (ch.privateChannels.image k) ((sourceState ns swap' left right extra ch phase).mapNames e k)) ∧
      r.Public (ns.restricted.image e) ∧ k c = c ∧
      ((sourceView ns swap left right phase).mapNames e).StaticEq ((sourceView ns swap' left right phase).mapNames e) ∧
      Named.JointOpening a (Named.restrictedState (ch.privateChannels.image k) ((sourceState ns swap left right extra ch phase).mapNames e k)) ∧
      Named.JointOpening d (Named.restrictedState (ch.privateChannels.image k) ((sourceState ns swap' left right extra ch phase).mapNames e k)) ∧
      ScopedStep (ch.privateChannels.image k) (ns.restricted.image e)
        ((sourceState ns swap left right extra ch phase).mapNames e k) (.input c r)
        ⟨(sourceView ns swap left right phase).mapNames e,q⟩ ∧
      Named.JointOpening b (Named.restrictedState (ch.privateChannels.image k)
        ⟨(sourceView ns swap left right phase).mapNames e,q⟩) := by
  have hs : (sourceView ns swap left right phase).StaticEq (sourceView ns swap' left right phase) := by
    have he := reachable_source_view_staticEq hf (hr.swap hf false)
    cases swap <;> cases swap'
    · exact .refl _
    · exact he
    · exact he.symm
    · exact .refl _
  exact ha.common_fresh_input (sourceState ns swap left right extra ch phase)
    (sourceState ns swap' left right extra ch phase) hd hs h
    (residual_visible_input_deterministic ns swap left right extra ch hc phase)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
