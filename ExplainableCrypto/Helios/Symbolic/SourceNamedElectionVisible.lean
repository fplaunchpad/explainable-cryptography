import ExplainableCrypto.Helios.Symbolic.SourceNamedCanonicalVisible

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- An actual Named input from any interpreted election body retains the
pending guard and waiting threads. Literal-recipe publicness is not inferred
from this statement; the fixed-policy stage rule still requires it. -/
theorem source_named_input_interpreted (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (phase : Process.Phase) (hr : phase.inRange extra)
    {a b : Named (Fin phase.handles)} {c : Nat} {r : Recipe phase.handles}
    (ha : a.Interprets NameAssignment.literal (sourceView ns swap left right phase).value
      (residual ns swap left right extra ch phase))
    (h : Named.FreeStep a (.input c r) b) (hc : c ∉ ch.privateChannels) :
    ∃ rs, phase = .input rs ∧ c = ch.voter (rs.length+2) ∧
      ∃ s : Recipe 3, HEq r s ∧
        b.Interprets NameAssignment.literal (sourceView ns swap left right phase).value
          (residual ns swap left right extra ch (.check rs s)) := by
  obtain ⟨q,hq,hb⟩ := h.input_interprets _ ha
  obtain ⟨body,hm⟩ := hq.input_prefix
  obtain ⟨rs,rfl,rfl,_⟩ := residual_public_input_prefix ns swap left right extra ch phase hr c body hc hm
  obtain ⟨rs',he,_,hp⟩ := (residual_public_input_iff ns swap left right extra ch (.input rs)
    hr _ r q hc).mp hq
  cases he
  exact ⟨rs,rfl,rfl,r,HEq.rfl,hb.congr (.of_parEq hp)⟩

/-- Every public Named bound output is one of the four actual publications.
The full payload, old/new environment and entire stage continuation are kept. -/
theorem source_named_output_interpreted (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (phase : Process.Phase) (hr : phase.inRange extra)
    {a : Named (Fin phase.handles)} {b : Named (Option (Fin phase.handles))} {c : Nat}
    (ha : a.Interprets NameAssignment.literal (sourceView ns swap left right phase).value
      (residual ns swap left right extra ch phase))
    (h : Named.BoundOutput a c b) (hc : c ∉ ch.privateChannels) :
    ∃ handle m next, Publication ns swap left right extra phase handle m next ∧
      c = ch.broadcast ∧ Process.Step ns swap left right extra phase (.output handle) next ∧
      HEq ((sourceView ns swap left right phase).extend m) (sourceView ns swap left right next) ∧
      b.Interprets NameAssignment.literal
        (extendEnv (sourceView ns swap left right phase).value m)
        (residual ns swap left right extra ch next) ∧
      (b.rename Extended.outputHandle).Interprets NameAssignment.literal
        ((sourceView ns swap left right phase).extend m).value
        (residual ns swap left right extra ch next) := by
  obtain ⟨m,q,hq,hb⟩ := h.literal_interprets _ ha
  obtain ⟨handle,next,hp,hc',he⟩ := (residual_public_output_iff ns swap left right extra ch
    phase hr c m q hc).mp hq
  have hb' := hb.congr (Agent.EvalEq.of_parEq he)
  refine ⟨handle,m,next,hp,hc',hp.stage,hp.capture,hb',?_⟩
  rw [Named.interprets_rename,Extended.outputHandle_environment]
  exact hb'

theorem source_named_canonical_input (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (phase : Process.Phase) (hr : phase.inRange extra)
    {b : Named (Fin phase.handles)} {c : Nat} {r : Recipe phase.handles}
    (h : Named.FreeStep (Named.restrictedState ch.privateChannels
      (sourceState ns swap left right extra ch phase)) (.input c r) b) :
    ∃ rs, phase = .input rs ∧ c = ch.voter (rs.length+2) ∧
      ∃ s : Recipe 3, HEq r s ∧
        b.Interprets NameAssignment.literal (sourceView ns swap left right phase).value
          (residual ns swap left right extra ch (.check rs s)) :=
  source_named_input_interpreted ns swap left right extra ch phase hr
    (Named.restrictedState_interprets _) h (Named.restricted_free_channel_public _ h)

theorem source_named_canonical_output (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (phase : Process.Phase) (hr : phase.inRange extra)
    {b : Named (Option (Fin phase.handles))} {c : Nat}
    (h : Named.BoundOutput (Named.restrictedState ch.privateChannels
      (sourceState ns swap left right extra ch phase)) c b) :
    ∃ handle m next, Publication ns swap left right extra phase handle m next ∧
      c = ch.broadcast ∧ Process.Step ns swap left right extra phase (.output handle) next ∧
      HEq ((sourceView ns swap left right phase).extend m) (sourceView ns swap left right next) ∧
      b.Interprets NameAssignment.literal
        (extendEnv (sourceView ns swap left right phase).value m)
        (residual ns swap left right extra ch next) ∧
      (b.rename Extended.outputHandle).Interprets NameAssignment.literal
        ((sourceView ns swap left right phase).extend m).value
        (residual ns swap left right extra ch next) :=
  source_named_output_interpreted ns swap left right extra ch phase hr
    (Named.restrictedState_interprets _) h (Named.restricted_bound_channel_public _ h)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
