import ExplainableCrypto.Helios.Symbolic.SourceCapturedViews

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- Exhaustive public-output correspondence for the evaluated election wrapper.
The captured frame retains the full payload and the target retains all threads. -/
theorem source_scoped_output_iff (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (hc : ch.Fresh) (phase : Process.Phase) (hr : phase.inRange extra)
    (c : Nat) (q : ScopedState ns.restricted (phase.handles+1)) :
    ScopedStep ch.privateChannels ns.restricted (sourceState ns swap left right extra ch phase) (.output c) q ↔
      ∃ handle m next, Publication ns swap left right extra phase handle m next ∧
        c=ch.broadcast ∧ q.frame=(sourceView ns swap left right phase).extend m ∧
        Agent.ParEq q.body (residual ns swap left right extra ch next) := by
  rw [scoped_output_iff]
  constructor
  · rintro ⟨hpub,m,hframe,hv⟩
    obtain ⟨handle,next,hout,he,hq⟩ := (residual_public_output_iff ns swap left right extra ch phase hr c m q.body hpub).mp hv
    exact ⟨handle,m,next,hout,he,hframe,hq⟩
  · rintro ⟨handle,m,next,hout,rfl,hframe,hq⟩
    refine ⟨Channels.broadcast_public hc,m,hframe,?_⟩
    exact Agent.Visible.congr (.refl _) (hout.visible ch) hq.symm

/-- Exhaustive recipe-input correspondence, including the phase-dependent
handle domain. A source input is possible only with three public handles. -/
theorem source_scoped_input_iff (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (hc : ch.Fresh) (phase : Process.Phase) (hr : phase.inRange extra)
    (c : Nat) (r : Recipe phase.handles) (q : ScopedState ns.restricted phase.handles) :
    ScopedStep ch.privateChannels ns.restricted (sourceState ns swap left right extra ch phase) (.input c r) q ↔
      r.Public ns.restricted ∧ ∃ rs, phase = .input rs ∧ c=ch.voter (rs.length+2) ∧
        ∃ s : Recipe 3, HEq r s ∧ q.frame=sourceView ns swap left right phase ∧
          Agent.ParEq q.body (residual ns swap left right extra ch (.check rs s)) := by
  constructor
  · intro h
    obtain ⟨hpub,hrecipe,hframe,hv⟩ := (scoped_input_iff _ _ _ _).mp h
    obtain ⟨body,hm⟩ := hv.input_prefix
    obtain ⟨rs,rfl,rfl,_⟩ := residual_public_input_prefix ns swap left right extra ch phase hr c body hpub hm
    refine ⟨hrecipe,rs,rfl,rfl,r,HEq.rfl,hframe.symm,?_⟩
    obtain ⟨rs',he,_,hq⟩ := (residual_public_input_iff ns swap left right extra ch (.input rs) hr _ r q.body hpub).mp hv
    cases he
    exact hq
  · rintro ⟨hrecipe,rs,rfl,rfl,s,he,hframe,hq⟩
    obtain rfl := eq_of_heq he
    apply (scoped_input_iff _ _ _ _).mpr
    refine ⟨(Channels.voter_public_iff hc _).mpr (by omega),hrecipe,hframe.symm,?_⟩
    exact Agent.Visible.congr (.refl _) (residual_visible_input ns swap left right extra ch rs r hr) hq.symm

/-- Every output captured by the wrapper agrees literally with its stage's
actual source view, even if parallel syntax in the continuation was rearranged. -/
theorem source_scoped_output_capture (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (hc : ch.Fresh) (phase : Process.Phase) (hr : phase.inRange extra)
    (c : Nat) (q : ScopedState ns.restricted (phase.handles+1))
    (h : ScopedStep ch.privateChannels ns.restricted (sourceState ns swap left right extra ch phase) (.output c) q) :
    ∃ handle next, Process.Step ns swap left right extra phase (.output handle) next ∧
      HEq q.frame (sourceView ns swap left right next) ∧
      Agent.ParEq q.body (residual ns swap left right extra ch next) := by
  obtain ⟨handle,m,next,hpub,_,he,hq⟩ := (source_scoped_output_iff ns swap left right extra ch hc phase hr c q).mp h
  exact ⟨handle,next,hpub.stage,he ▸ hpub.capture,hq⟩
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
