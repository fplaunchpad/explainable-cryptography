import ExplainableCrypto.Helios.Symbolic.SourceCoordinatedInternal
import ExplainableCrypto.Helios.Symbolic.SourceCoordinatedFreshInput
import ExplainableCrypto.Helios.Symbolic.SourceIndependentFrameCompatibility

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {restricted restricted' hidden hidden' : Finset Nat} {handles : Nat}

/-- Actual whole-state structural freshening transports the complete canonical
frame presentation, including its private policies and all handle values. -/
theorem RepresentsFrame.transport_state_structure {a : Named (Fin handles)}
    {p : ScopedState restricted handles} {q : ScopedState restricted' handles}
    (ha : a.RepresentsFrame hidden p.frame)
    (h : Structural (restrictedState hidden p) (restrictedState hidden' q)) :
    a.RepresentsFrame hidden' q.frame :=
  ha.trans ((restrictedState_frameOf hidden p).symm.trans
    (h.frameOf.trans (restrictedState_frameOf hidden' q)))

/-- Handle equality transports an actual mapped presentation without changing
any frame value or policy. This is the cast used by internal phase successors. -/
theorem RepresentsFrame.cast_mapped_handles {before after : Nat}
    {a : Named (Fin before)} {φ : Frame restricted before} {ψ : Frame restricted after}
    (e : Nat ≃ Nat) (h : a.RepresentsFrame hidden (φ.mapNames e))
    (hh : before = after) (he : HEq φ ψ) :
    (a.rename (Fin.cast hh)).RepresentsFrame hidden (ψ.mapNames e) := by
  subst after
  cases he
  simpa only [show Fin.cast (Eq.refl before) = (id : Fin before → Fin before) from rfl,rename_id] using h

/-- The current actual presentations, rather than just semantic comparisons,
survive common input freshening and the original raw input action. -/
theorem JointOpening.common_fresh_input_presented (p t : ScopedState restricted handles)
    {a b d : Named (Fin handles)}
    (ha : JointOpening a (restrictedState hidden p))
    (hd : JointOpening d (restrictedState hidden t)) (hs : p.frame.StaticEq t.frame)
    (hpa : a.RepresentsFrame hidden p.frame) (hpd : d.RepresentsFrame hidden t.frame)
    {c : Nat} {r : Recipe handles} (h : FreeStep a (.input c r) b)
    (hdet : ∀ c m q s, Agent.Visible p.body (.input c m) q → Agent.Visible p.body (.input c m) s → Agent.EvalEq q s) :
    ∃ (e k : Nat ≃ Nat) (q : Agent Empty),
      r.Public (restricted.image e) ∧ k c = c ∧
      (p.frame.mapNames e).StaticEq (t.frame.mapNames e) ∧
      JointOpening a (restrictedState (hidden.image k) (p.mapNames e k)) ∧
      JointOpening d (restrictedState (hidden.image k) (t.mapNames e k)) ∧
      ScopedStep (hidden.image k) (restricted.image e) (p.mapNames e k) (.input c r)
        ⟨p.frame.mapNames e,q⟩ ∧
      JointOpening b (restrictedState (hidden.image k) ⟨p.frame.mapNames e,q⟩) ∧
      a.RepresentsFrame (hidden.image k) (p.frame.mapNames e) ∧
      d.RepresentsFrame (hidden.image k) (t.frame.mapNames e) ∧
      b.RepresentsFrame (hidden.image k) (p.frame.mapNames e) := by
  obtain ⟨e,k,q,hp,ht,hr,hk,he,ha',hd',hstep,hb⟩ := ha.common_fresh_input p t hd hs h hdet
  have hpa' := hpa.transport_state_structure hp
  have hpd' := hpd.transport_state_structure ht
  exact ⟨e,k,q,hr,hk,he,ha',hd',hstep,hb,hpa',hpd',hpa'.free h⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- Internal phase transitions retain the actual full presentation, including
acceptance, rejection and private communication. No target witness is assumed. -/
theorem source_coordinated_internal_presented_next (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (e k : Nat ≃ Nat) (phase : Process.Phase) (hr : Process.Reachable ns swap left right extra phase)
    {a b : Named (Fin phase.handles)}
    (ha : Named.JointOpening a (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k))
    (hp : a.RepresentsFrame (ch.privateChannels.image k) ((sourceView ns swap left right phase).mapNames e))
    (h : Named.Reduction a b) :
    ∃ (next : Process.Phase) (hh : phase.handles = next.handles),
      Process.Step ns swap left right extra phase .tau next ∧
      Process.Reachable ns swap left right extra next ∧
      Named.JointOpening (b.rename (Fin.cast hh))
        (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch next) e k) ∧
      (b.rename (Fin.cast hh)).RepresentsFrame (ch.privateChannels.image k)
        ((sourceView ns swap left right next).mapNames e) := by
  obtain ⟨next,hh,hs,hb⟩ := source_coordinated_internal_next ns swap left right extra ch hc
    e k phase hr.wellFormed.inRange ha h
  exact ⟨next,hh,hs,hr.tail ⟨.tau,hs⟩,hb,
    (hp.internal h).cast_mapped_handles e hh hs.tau_sourceView⟩

/-- The reachable-election input branch retains actual raw frame presentations
at the refreshed policy. Every freshness and phase-classification condition is
derived; the current actual presentation is the induction hypothesis. -/
theorem source_coordinated_input_presented_next (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (e k : Nat ≃ Nat) (phase : Process.Phase) (hr : Process.Reachable ns swap left right extra phase)
    {a b d : Named (Fin phase.handles)}
    (ha : Named.JointOpening a (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k))
    (hd : Named.JointOpening d (Named.mappedState ch.privateChannels (sourceState ns swap' left right extra ch phase) e k))
    (hpa : a.RepresentsFrame (ch.privateChannels.image k) ((sourceView ns swap left right phase).mapNames e))
    (hpd : d.RepresentsFrame (ch.privateChannels.image k) ((sourceView ns swap' left right phase).mapNames e))
    {c : Nat} {r : Recipe phase.handles} (h : Named.FreeStep a (.input c r) b) :
    ∃ (f l : Nat ≃ Nat) (rs : List (Recipe 3)) (s : Recipe 3),
      phase = .input rs ∧ HEq (r.mapNames (e.trans f).symm) s ∧ s.Public ns.restricted ∧
      c = (k.trans l) (ch.voter (rs.length+2)) ∧
      Process.Step ns swap left right extra phase (.input (rs.length+2) s) (.check rs s) ∧
      Process.Reachable ns swap left right extra (.check rs s) ∧
      CoordinatedPhaseOpening ns swap left right extra ch (e.trans f) (k.trans l) (.check rs s) b ∧
      b.RepresentsFrame (ch.privateChannels.image (k.trans l))
        ((sourceView ns swap left right phase).mapNames (e.trans f)) ∧
      d.RepresentsFrame (ch.privateChannels.image (k.trans l))
        ((sourceView ns swap' left right phase).mapNames (e.trans f)) ∧
      Named.JointOpening d (Named.mappedState ch.privateChannels
        (sourceState ns swap' left right extra ch phase) (e.trans f) (k.trans l)) ∧
      Named.StaticEq b d := by
  have hs : (sourceView ns swap left right phase).StaticEq (sourceView ns swap' left right phase) := by
    have he := reachable_source_view_staticEq hf (hr.swap hf false)
    cases swap <;> cases swap'
    · exact .refl _
    · exact he
    · exact he.symm
    · exact .refl _
  obtain ⟨f,l,q,hpub,_,he,ha',hdJoint,_,_,_,hd',hb'⟩ := ha.common_fresh_input_presented
    ((sourceState ns swap left right extra ch phase).mapNames e k)
    ((sourceState ns swap' left right extra ch phase).mapNames e k) hd (hs.mapNames e) hpa hpd h
    (Agent.input_determinism_mapNames _ (residual_visible_input_deterministic ns swap left right extra ch hc phase) e k)
  have ha'' : Named.JointOpening a (Named.mappedState ch.privateChannels
      (sourceState ns swap left right extra ch phase) (e.trans f) (k.trans l)) := by
    rw [← Named.mappedState_comp]
    exact ha'
  have hdJoint' : Named.JointOpening d (Named.mappedState ch.privateChannels
      (sourceState ns swap' left right extra ch phase) (e.trans f) (k.trans l)) := by
    rw [← Named.mappedState_comp]
    exact hdJoint
  have hpub' : r.Public (ns.restricted.image (e.trans f)) := by
    simpa only [Finset.image_image,Equiv.coe_trans] using hpub
  obtain ⟨rs,s,hphase,hrcp,hsp,hchan,hstep,ht⟩ := source_coordinated_public_input_next
    ns swap left right extra ch hc (e.trans f) (k.trans l) phase hr.wellFormed.inRange ha'' h hpub'
  have hb'' : b.RepresentsFrame (ch.privateChannels.image (k.trans l))
      ((sourceView ns swap left right phase).mapNames (e.trans f)) := by
    simpa only [Named.RepresentsFrame,Named.canonicalFrame,Extended.activeFrame,ScopedState.mapNames,sourceState,Frame.mapNames,Term.mapNames_comp,Finset.image_image,Equiv.coe_trans] using hb'
  have hd'' : d.RepresentsFrame (ch.privateChannels.image (k.trans l))
      ((sourceView ns swap' left right phase).mapNames (e.trans f)) := by
    simpa only [Named.RepresentsFrame,Named.canonicalFrame,Extended.activeFrame,ScopedState.mapNames,sourceState,Frame.mapNames,Term.mapNames_comp,Finset.image_image,Equiv.coe_trans] using hd'
  exact ⟨f,l,rs,s,hphase,hrcp,hsp,hchan,hstep,hr.tail ⟨_,hstep⟩,ht,hb'',hd'',hdJoint',
    Named.StaticEq.of_presentations hb'' hd'' (hs.mapNames (e.trans f))⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
