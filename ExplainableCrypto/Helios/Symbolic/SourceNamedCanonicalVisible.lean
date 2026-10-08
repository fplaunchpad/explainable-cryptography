import ExplainableCrypto.Helios.Symbolic.SourceNamedVisibleInterpretation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {restricted hidden : Finset Nat} {handles : Nat}

theorem FreeStep.canonical_input (s : ScopedState restricted handles)
    {b : Named (Fin handles)} {c : Nat} {r : Recipe handles}
    (h : FreeStep (restrictedState hidden s) (.input c r) b) :
    ∃ q, Agent.Visible s.body (.input c (s.frame.eval r)) q ∧
      b.Interprets NameAssignment.literal s.frame.value q :=
  h.input_interprets s.frame.value (restrictedState_interprets s)

/-- Publicness is explicit: alpha can make an old private numeral available in
a source input, so this fixed-policy wrapper theorem retains its recipe premise. -/
theorem FreeStep.canonical_input_scoped (s : ScopedState restricted handles)
    {b : Named (Fin handles)} {c : Nat} {r : Recipe handles}
    (h : FreeStep (restrictedState hidden s) (.input c r) b) (hr : r.Public restricted) :
    ∃ q : ScopedState restricted handles,
      ScopedStep hidden restricted s (.input c r) q ∧ q.frame = s.frame ∧
      b.Interprets NameAssignment.literal q.frame.value q.body ∧ b.RepresentsFrame hidden q.frame := by
  obtain ⟨q,hq,hb⟩ := h.canonical_input s
  exact ⟨⟨s.frame,q⟩,(scoped_input_iff _ _ _ _).mpr
    ⟨restricted_free_channel_public s h,hr,rfl,hq⟩,rfl,hb,(restrictedState_represents s).free h⟩

theorem BoundOutput.canonical_output (s : ScopedState restricted handles)
    {b : Named (Option (Fin handles))} {c : Nat}
    (h : BoundOutput (restrictedState hidden s) c b) :
    ∃ m q, Agent.Visible s.body (.output c m) q ∧
      b.Interprets NameAssignment.literal (extendEnv s.frame.value m) q ∧
      (b.rename Extended.outputHandle).Interprets NameAssignment.literal (s.frame.extend m).value q := by
  obtain ⟨m,q,hq,hb⟩ := h.literal_interprets s.frame.value (restrictedState_interprets s)
  refine ⟨m,q,hq,hb,?_⟩
  rw [interprets_rename,Extended.outputHandle_environment]
  exact hb

/-- Every actual bound output gives an evaluated scoped output and the complete
raw target interpretation after fresh-handle renaming. This does not assert a
structural canonical presentation of the target's new frame. -/
theorem BoundOutput.canonical_output_scoped (s : ScopedState restricted handles)
    {b : Named (Option (Fin handles))} {c : Nat}
    (h : BoundOutput (restrictedState hidden s) c b) :
    ∃ (m : Ground) (q : ScopedState restricted (handles+1)),
      ScopedStep hidden restricted s (.output c) q ∧ q.frame = s.frame.extend m ∧
      b.Interprets NameAssignment.literal (extendEnv s.frame.value m) q.body ∧
      (b.rename Extended.outputHandle).Interprets NameAssignment.literal q.frame.value q.body := by
  obtain ⟨m,q,hq,hb,hb'⟩ := h.canonical_output s
  exact ⟨m,⟨s.frame.extend m,q⟩,(scoped_output_iff _ _ _).mpr
    ⟨restricted_bound_channel_public s h,m,rfl,hq⟩,rfl,hb,hb'⟩

/-- Coherent freshening removes the fixed recipe-policy premise while keeping
the actual source input label and target unchanged. Both worlds retain their
full frame observations under the same permutations. -/
theorem FreeStep.common_fresh_canonical_input (s t : ScopedState restricted handles)
    {b : Named (Fin handles)} {c : Nat} {r : Recipe handles}
    (h : FreeStep (restrictedState hidden s) (.input c r) b) (he : s.frame.StaticEq t.frame) :
    ∃ e k : Nat ≃ Nat,
      Structural (restrictedState hidden s) (restrictedState (hidden.image k) (s.mapNames e k)) ∧
      Structural (restrictedState hidden t) (restrictedState (hidden.image k) (t.mapNames e k)) ∧
      r.Public (restricted.image e) ∧ k c = c ∧
      (s.frame.mapNames e).StaticEq (t.frame.mapNames e) ∧
      ∃ q : ScopedState (restricted.image e) handles,
        ScopedStep (hidden.image k) (restricted.image e) (s.mapNames e k) (.input c r) q ∧
        q.frame = s.frame.mapNames e ∧
        b.Interprets NameAssignment.literal q.frame.value q.body ∧
        b.RepresentsFrame (hidden.image k) q.frame := by
  obtain ⟨e,k,hs,ht,hr,hc,he',h'⟩ := input_action_common_fresh_states s t c r b h he
  exact ⟨e,k,hs,ht,hr,hc,he',h'.canonical_input_scoped (s.mapNames e k) hr⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
