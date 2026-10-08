import ExplainableCrypto.Helios.Symbolic.SourceInterpretationBound

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type} {restricted restricted' : Finset Nat} {handles : Nat}

theorem frameProcess_input_interpreted (φ : Frame restricted handles) (p : Agent Empty)
    {b : Extended (Fin handles)} {c : Nat} {r : Recipe handles}
    (h : FreeStep (frameProcess φ p) (.input c r) b) :
    ∃ q, Agent.Visible p (.input c (φ.eval r)) q ∧ b.Realizes φ.value q :=
  h.input_realizes φ.value (frameProcess_realizes φ p)

theorem frameProcess_input_values (φ : Frame restricted handles) (ψ : Frame restricted' handles)
    (p q : Agent Empty) {c : Nat} {r : Recipe handles}
    (h : FreeStep (frameProcess φ p) (.input c r) (frameProcess ψ q)) :
    (∀ i, EqE (φ.value i) (ψ.value i)) ∧
      ∃ s, Agent.Visible p (.input c (φ.eval r)) s ∧ Agent.EvalEq q s := by
  obtain ⟨s,hs,he⟩ := frameProcess_input_interpreted φ p h
  obtain ⟨hv,hq⟩ := (frameProcess_realizes_iff ψ q φ.value s).mp he
  exact ⟨hv,s,hs,hq⟩

theorem frameProcess_input_staticEq (φ ψ : Frame restricted handles) (p q : Agent Empty)
    {c : Nat} {r : Recipe handles}
    (h : FreeStep (frameProcess φ p) (.input c r) (frameProcess ψ q)) : φ.StaticEq ψ :=
  Frame.staticEq_of_pointwise (frameProcess_input_values φ ψ p q h).1

theorem frameProcess_output_interpreted (φ : Frame restricted handles) (p : Agent Empty)
    {b : Extended (Fin handles)} {c : Nat} {x : Fin handles}
    (h : FreeStep (frameProcess φ p) (.output c x) b) :
    ∃ m q, EqE (φ.value x) m ∧ Agent.Visible p (.output c m) q ∧ b.Realizes φ.value q :=
  h.output_realizes φ.value (frameProcess_realizes φ p)

theorem outputHandle_environment (φ : Frame restricted handles) (m : Ground) :
    (fun v => (φ.extend m).value (outputHandle v)) = extendEnv φ.value m := by
  funext v
  cases v with
  | none => simpa only [outputHandle_none,extendEnv] using Frame.extend_last φ m
  | some v => simpa only [outputHandle_some,extendEnv] using Frame.extend_old φ m v

/-- Bound output is interpreted under precisely the old frame extended with
the emitted message, before and after its canonical fresh-handle renaming. -/
theorem frameProcess_bound_interpreted (φ : Frame restricted handles) (p : Agent Empty)
    {b : Extended (Option (Fin handles))} {c : Nat}
    (h : BoundOutput (frameProcess φ p) c b) :
    ∃ m q, Agent.Visible p (.output c m) q ∧
      b.Realizes (extendEnv φ.value m) q ∧
      (b.rename outputHandle).Realizes (φ.extend m).value q := by
  obtain ⟨m,q,hq,he⟩ := h.realizes φ.value (frameProcess_realizes φ p)
  refine ⟨m,q,hq,he,?_⟩
  rw [realizes_rename,outputHandle_environment]
  exact he

/-- Any supplied canonical target must retain every old handle and the full
new output value modulo E; the body relates to an actual visible continuation. -/
theorem frameProcess_bound_values (φ : Frame restricted handles)
    (ψ : Frame restricted' (handles+1)) (p q : Agent Empty)
    {b : Extended (Option (Fin handles))} {c : Nat}
    (h : BoundOutput (frameProcess φ p) c b)
    (ht : Structural (b.rename outputHandle) (frameProcess ψ q)) :
    ∃ m s, Agent.Visible p (.output c m) s ∧
      (∀ i, EqE ((φ.extend m).value i) (ψ.value i)) ∧ Agent.EvalEq q s := by
  obtain ⟨m,s,hs,_,he⟩ := frameProcess_bound_interpreted φ p h
  obtain ⟨hv,hq⟩ := (frameProcess_realizes_iff ψ q (φ.extend m).value s).mp
    ((ht.realizes (φ.extend m).value s).mp he)
  exact ⟨m,s,hs,hv,hq⟩

theorem frameProcess_bound_staticEq (φ : Frame restricted handles)
    (ψ : Frame restricted (handles+1)) (p q : Agent Empty)
    {b : Extended (Option (Fin handles))} {c : Nat}
    (h : BoundOutput (frameProcess φ p) c b)
    (ht : Structural (b.rename outputHandle) (frameProcess ψ q)) :
    ∃ m s, Agent.Visible p (.output c m) s ∧ (φ.extend m).StaticEq ψ ∧ Agent.EvalEq q s := by
  obtain ⟨m,s,hs,hv,hq⟩ := frameProcess_bound_values φ ψ p q h ht
  exact ⟨m,s,hs,Frame.staticEq_of_pointwise hv,hq⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
