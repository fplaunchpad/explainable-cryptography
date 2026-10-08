import ExplainableCrypto.Helios.Symbolic.SourceFrameInternal
import ExplainableCrypto.Helios.Symbolic.SourceAtomicOutputSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceFrameInputSPOT
open Historical General Source Extended

def policy : Finset Nat := {40}
def publicFrame : Frame policy 2 := ⟨fun i => if i=0 then .unary .pk (.name 40) else .name 41⟩
def received : Recipe 2 := .binary .pair (.var 1) (.var 0)
def continuation : Agent (Option Empty) := .input 6
  (.output 7 (.binary .pair (.var (some none)) (.var none)) .nil)
def expected : Agent Empty := .input 6
  (.output 7 (.binary .pair (.binary .pair (.name 41) (.unary .pk (.name 40))) (.var none)) .nil)

/-- Independent expected value: the recipe reverses the two handle positions,
and the opaque public-key handle may contain a restricted atom. -/
theorem compound_recipe_value : publicFrame.eval received =
    .binary .pair (.name 41) (.unary .pk (.name 40)) := rfl

/-- The later input variable is distinct from the compound value received now. -/
theorem nested_received_value : continuation.bind (publicFrame.eval received) = expected := rfl

/-- In carries the original handle recipe, while source Subst evaluates the
received value without changing the frame or the subsequent input binder. -/
theorem compound_source_input :
    FreeStep (frameProcess publicFrame (.par (.input 4 continuation) .nil)) (.input 4 received)
      (frameProcess publicFrame (.par expected .nil)) :=
  frame_input_in_context publicFrame 4 continuation .nil received

/-- Reversing the handle environment does not yield the same received value. -/
theorem reversed_handles_detected :
    publicFrame.eval received ≠ (.binary .pair (.unary .pk (.name 40)) (.name 41) : Ground) := by
  intro h
  cases h

/-- Substitution may not overwrite the newer local input variable. -/
theorem nested_capture_detected : continuation.bind (publicFrame.eval received) ≠
    (.input 6 (.output 7 (.binary .pair (.var none) (.var none)) .nil) : Agent Empty) := by
  intro h
  simp [continuation,Agent.bind,Agent.subst,liftSubst,inputSubst,Term.subst,publicFrame,received,Frame.eval] at h

/-- The frame evaluates all uses in a plain process; both active bindings remain
in the source term after the structural substitution derivation. -/
theorem active_substitution_preserves_bindings :
    Structural (.par (activeFrame publicFrame) (.plain (.output 7 received .nil)))
      (.par (activeFrame publicFrame) (.plain (.output 7
        (.binary .pair (.name 41) (.unary .pk (.name 40))) .nil))) :=
  activeFrame_apply publicFrame (.output 7 received .nil)

/-- A source input cannot discard the existing exported frame bindings. -/
theorem dropped_input_frame_blocked :
    ¬ FreeStep (frameProcess publicFrame (.input 4 continuation)) (.input 4 received)
      (.plain (groundAgent expected)) := by
  intro h
  have he := h.exports 0
  simp [frameProcess,activeFrame,frameEntries,Exports] at he

/-- Publicness checks the literal recipe; opaque values reached through public
handles remain allowed, whereas a literal restricted name is forbidden. -/
theorem handle_public_literal_private :
    received.Public policy ∧ ¬ (Term.name 40 : Recipe 2).Public policy := by
  refine ⟨⟨True.intro,True.intro⟩,?_⟩
  intro h
  exact h (by simp [policy])

/-- Equal-valued handles are allowed. Injectivity concerns the variable names,
not payload inequality; both substitutions still have their exact value. -/
theorem equal_values_at_distinct_handles :
    entriesSubst 2 id (fun _ => (.name 41 : Ground)) (0 : Fin 2) = groundTerm (.name 41) ∧
    entriesSubst 2 id (fun _ => (.name 41 : Ground)) (1 : Fin 2) = groundTerm (.name 41) :=
  ⟨entriesSubst_value _ _ _ Function.injective_id _,entriesSubst_value _ _ _ Function.injective_id _⟩

/-- The actual next voter label stays var 1 in the source derivation and reaches
the pending replay guard before the later rejecting internal transition. -/
theorem honest_replay_source_input (swap : Bool) :
    FreeStep (frameProcess (SharedTallySPOT.world swap)
      (residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical (.input [])))
      (.input 4 (.var 1))
      (frameProcess (SharedTallySPOT.world swap)
        (residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical (.check [] (.var 1)))) :=
  scoped_input_derivable _ _ _ _ _ (SourceScopedSPOT.actual_voter_input swap)

/-- Actual private honest communication derives beside the retained initial
public-key frame; its source internal rule does not export or replace a handle. -/
theorem honest_receive_keeps_active_frame (swap : Bool) :
    Reduction
      (frameProcess (sourceView SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right .start)
        (residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical .start))
      (frameProcess (sourceView SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right .firstReceived)
        (residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical .firstReceived)) :=
  scoped_tau_derivable Channels.canonical.privateChannels _ _
    (.tau _ (residual_receiveFirst _ _ _ _ _ _))
end ExplainableCrypto.Helios.Symbolic.SourceFrameInputSPOT
