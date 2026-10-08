import ExplainableCrypto.Helios.Symbolic.SourceNameFrames

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {restricted hidden : Finset Nat} {before after : Nat}

def ScopedState.mapNames (p : ScopedState restricted before) (f g : Nat → Nat) :
    ScopedState (restricted.image f) before := ⟨p.frame.mapNames f,p.body.mapNames f g⟩

def PublicEvent.mapNames (f g : Nat → Nat) : {before after : Nat} → PublicEvent before after → PublicEvent before after
  | _, _, .tau => .tau
  | _, _, .input c r => .input (g c) (r.mapNames f)
  | _, _, .output c => .output (g c)

theorem channel_public_mapNames_iff (c : Nat) (hidden : Finset Nat) (k : Nat ≃ Nat) :
    k c ∉ hidden.image k ↔ c ∉ hidden := by
  simp [k.injective.eq_iff]

theorem ScopedStep.mapNames {p : ScopedState restricted before} {q : ScopedState restricted after}
    {l : PublicEvent before after} (h : ScopedStep hidden restricted p l q) (e k : Nat ≃ Nat) :
    ScopedStep (hidden.image k) (restricted.image e) (p.mapNames e k) (l.mapNames e k) (q.mapNames e k) := by
  cases h with
  | tau φ h => exact .tau _ (h.mapNames e k)
  | input φ c r hc hr h =>
    apply ScopedStep.input _ _ _ ((channel_public_mapNames_iff c hidden k).mpr hc)
      ((Term.public_mapNames_iff r e restricted).mpr hr)
    simpa only [Frame.mapNames_eval,Agent.PayloadEvent.mapNames] using h.mapNames e k
  | output φ c m hc h =>
    simpa only [ScopedState.mapNames,PublicEvent.mapNames,Frame.mapNames_extend] using
      ScopedStep.output (hidden := hidden.image k) (φ.mapNames e) (k c) (m.mapNames e)
        ((channel_public_mapNames_iff c hidden k).mpr hc) (h.mapNames e k)

/-- Every renamed scoped action reflects to its original action, with full
frame equality and output payloads; output labels still contain only a channel. -/
theorem scopedStep_mapNames_iff (p : ScopedState restricted before) (q : ScopedState restricted after)
    (l : PublicEvent before after) (e k : Nat ≃ Nat) :
    ScopedStep (hidden.image k) (restricted.image e) (p.mapNames e k) (l.mapNames e k) (q.mapNames e k) ↔
      ScopedStep hidden restricted p l q := by
  constructor
  · intro h
    cases l with
    | tau =>
      obtain ⟨hf,ht⟩ := (scoped_tau_iff _ _).mp h
      exact (scoped_tau_iff _ _).mpr ⟨Frame.mapNames_injective e hf,(Agent.Tau.mapNames_iff _ _ e k).mp ht⟩
    | input c r =>
      obtain ⟨hc,hr,hf,hv⟩ := (scoped_input_iff _ _ _ _).mp h
      refine (scoped_input_iff _ _ _ _).mpr ⟨(channel_public_mapNames_iff c hidden k).mp hc,
        (Term.public_mapNames_iff r e restricted).mp hr,Frame.mapNames_injective e hf,?_⟩
      apply (Agent.Visible.mapNames_iff _ _ (.input c (p.frame.eval r)) e k).mp
      simpa only [ScopedState.mapNames,Frame.mapNames_eval,Agent.PayloadEvent.mapNames] using hv
    | output c =>
      obtain ⟨hc,m,hf,hv⟩ := (scoped_output_iff _ _ _).mp h
      refine (scoped_output_iff _ _ _).mpr ⟨(channel_public_mapNames_iff c hidden k).mp hc,m.mapNames e.symm,?_,?_⟩
      · apply Frame.mapNames_injective e
        simpa only [ScopedState.mapNames,Frame.mapNames_extend,show (m.mapNames e.symm).mapNames e = m from Term.mapNames_inverse m e.symm] using hf
      · apply (Agent.Visible.mapNames_iff _ _ (.output c (m.mapNames e.symm)) e k).mp
        simpa only [ScopedState.mapNames,Agent.PayloadEvent.mapNames,show (m.mapNames e.symm).mapNames e = m from Term.mapNames_inverse m e.symm] using hv
  · exact fun h => h.mapNames e k
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
