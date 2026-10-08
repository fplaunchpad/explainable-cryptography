import ExplainableCrypto.Helios.Symbolic.SourceVisibleElection
import ExplainableCrypto.Helios.Symbolic.SourceInternalSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceScopedSPOT
open Historical General Source
abbrev ch := Channels.canonical
abbrev policy : Finset Nat := {40}
def publicFrame : Frame policy 1 := ⟨fun _ => .unary .pk (.name 40)⟩
abbrev echo : Agent (Option Empty) := .output 0 (.var none) .nil
abbrev emitting : ScopedState policy 1 := ⟨publicFrame,.output 0 (.name 40) .nil⟩
abbrev emitted : ScopedState policy 2 := ⟨publicFrame.extend (.name 40),.nil⟩

/-- A deliberately revealing process really exports its secret value. The
restriction wrapper does not hide a leak by redacting the public frame. -/
theorem output_exposes_full_value :
    ScopedStep ch.privateChannels policy emitting (.output 0) emitted ∧
    emitted.frame.value 1 = .name 40 ∧ emitted.frame.value 0 = .unary .pk (.name 40) := by
  refine ⟨?_,rfl,rfl⟩
  exact .output publicFrame 0 (.name 40) (by decide) (Agent.Visible.of_core (.output _ _ _))

/-- The new handle cannot overwrite the previous public key handle. -/
theorem output_handle_does_not_alias : (Fin.last 1) ≠ (0 : Fin 1).castSucc := output_handle_fresh _

/-- Every old expression keeps its value after this concrete output. -/
theorem output_retains_old_recipes (r : Recipe 1) : emitted.frame.eval r.lift = publicFrame.eval r :=
  scoped_output_preserves_old output_exposes_full_value.1 r

/-- Replacing the emitted secret by bottom is rejected by the operational rules. -/
theorem redacted_output_mutant_rejected :
    ¬ ScopedStep ch.privateChannels policy emitting (.output 0)
      (⟨publicFrame.extend (.const .bottom),.nil⟩ : ScopedState policy 2) := by
  intro h
  obtain ⟨_,m,he,hv⟩ := (scoped_output_iff _ _ _).mp h
  obtain ⟨body,hm⟩ := hv.output_prefix
  simp [Agent.threads,Agent.threadList] at hm
  rw [hm.1] at he
  have hh := congrArg (fun f : Frame policy 2 => f.value (Fin.last 1)) he
  simp only [Frame.extend_last] at hh
  cases hh

/-- Public handles may denote terms containing restricted atoms. Recipe input
must evaluate the handle, rather than reject its resulting opaque key term. -/
theorem public_handle_input_evaluates :
    ScopedStep ch.privateChannels policy (⟨publicFrame,.input 4 echo⟩ : ScopedState policy 1)
      (.input 4 (.var 0)) ⟨publicFrame,.output 0 (.unary .pk (.name 40)) .nil⟩ :=
  .input publicFrame 4 (.var 0) (by decide) (by trivial) (Agent.Visible.of_core (.input _ _ _))

/-- A literal restricted name is not an authorized public input recipe. -/
theorem restricted_literal_input_blocked (q : ScopedState policy 1) :
    ¬ ScopedStep ch.privateChannels policy (⟨publicFrame,.input 4 echo⟩ : ScopedState policy 1)
      (.input 4 (.name 40)) q := by
  intro h
  have hr := ((scoped_input_iff _ _ _ _).mp h).2.1
  exact hr (by simp [policy])

/-- Both visible directions on the trustee channel are blocked. -/
theorem private_actions_blocked (r : Recipe 1) (p q : ScopedState policy 1) (q' : ScopedState policy 2) :
    ¬ ScopedStep ch.privateChannels policy p (.input 1 r) q ∧
    ¬ ScopedStep ch.privateChannels policy p (.output 1) q' :=
  ⟨scoped_private_input_blocked _ _ _ _ (Channels.trustee_private ch),
    scoped_private_output_blocked _ _ _ (Channels.trustee_private ch)⟩

/-- The private restriction still permits communication inside the process. -/
theorem private_handshake_preserved :
    ScopedStep ch.privateChannels policy
      (⟨publicFrame,.par (.output 1 (.name 41) .nil) (.input 1 echo)⟩ : ScopedState policy 1)
      .tau ⟨publicFrame,.par .nil (.output 0 (.name 41) .nil)⟩ :=
  .tau publicFrame (Agent.Tau.of_core (.comm _ _ _ _))

/-- Visible closure cannot expose the later sequential output first. -/
theorem hidden_output_not_visible (q : Agent Empty) :
    ¬ Agent.Visible (.output 0 (.name 40) (.output 0 (.name 41) .nil)) (.output 0 (.name 41)) q := by
  intro h
  obtain ⟨body,hm⟩ := h.output_prefix
  simp [Agent.threads,Agent.threadList] at hm

/-- An actual submitted ballot reaches the guard with the same three-handle
frame, on the third voter's public channel, before acceptance is decided. -/
theorem actual_voter_input (swap : Bool) :
    ScopedStep ch.privateChannels SharedTallySPOT.names.restricted
      ⟨SharedTallySPOT.world swap,residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right
        1 ch (.input [])⟩ (.input 4 (.var 1))
      ⟨SharedTallySPOT.world swap,residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right
        1 ch (.check [] (.var 1))⟩ :=
  residual_scoped_input _ _ _ _ _ _ Channels.canonical_fresh _ _ (by decide) (by trivial)

/-- The actual rejected residual has no internal or public labelled step in
this wrapper; the trustee's syntax is retained rather than erased. -/
theorem actual_rejected_process_stops (swap : Bool) {after : Nat} (a : PublicEvent 3 after)
    (q : ScopedState SharedTallySPOT.names.restricted after) :
    ¬ ScopedStep ch.privateChannels SharedTallySPOT.names.restricted
      ⟨SharedTallySPOT.world swap,residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right
        1 ch (.rejected [])⟩ a q :=
  rejected_no_scoped_step _ _ _ _ _ _ _ _ a q
end ExplainableCrypto.Helios.Symbolic.SourceScopedSPOT
