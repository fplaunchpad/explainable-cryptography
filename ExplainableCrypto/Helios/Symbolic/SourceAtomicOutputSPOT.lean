import ExplainableCrypto.Helios.Symbolic.SourceOutputDerivation
import ExplainableCrypto.Helios.Symbolic.SourceActiveBindingSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceAtomicOutputSPOT
open Historical General Source Extended

/-- A deliberately secret-revealing output really exports the secret. This is
an operational model control, not a claim of a leak in the election. -/
theorem secret_output_exports_literal :
    BoundOutput (.plain (.output 0 (.name 40) .nil) : Extended Empty) 0
      (.par (.active none (.name 40)) (.plain .nil)) :=
  message_output 0 (.name 40) .nil

/-- A compound output retains the existing outer variable in its payload,
shifted separately from the fresh exported binder. -/
theorem compound_output_retains_outer_variable :
    BoundOutput (.plain (.output 0 SourceActiveBindingSPOT.message .nil)) 0
      (.par (.active none (.binary .pair (.name 40) (.var (some (0 : Fin 1))))) (.plain .nil)) :=
  message_output 0 SourceActiveBindingSPOT.message .nil

/-- Fresh export through an enclosing local restriction exchanges the binder
positions: the local stays restricted, and the new output becomes public. -/
theorem output_crosses_variable_scope :
    BoundOutput
      (.newVar (.par (.active none (.name 40)) (.plain (.output 0 (.name 41) .nil))) : Extended (Fin 1)) 0
      (.newVar (.par (.active none (.name 40)) (.par (.active (some none) (.name 41)) (.plain .nil)))) := by
  exact .scope (.parRight _ (message_output 0 (.name 41) .nil))

/-- The exported variable survives the enclosing restriction in that fixture. -/
theorem crossed_output_is_exported :
    (Extended.newVar (.par (.active none (.name 40))
      (.par (.active (some none) (.name 41)) (.plain .nil))) : Extended (Option (Fin 1))).Exports none :=
  Or.inr (Or.inl rfl)

/-- An old active handle cannot disappear while a new variable is exported. -/
theorem dropped_old_export_blocked :
    ¬ BoundOutput (.par (.active (0 : Fin 1) (.name 40)) (.plain (.output 0 (.name 41) .nil))) 0
      (.par (.active none (.name 41)) (.plain .nil)) := by
  intro h
  have he := h.old_exports 0
  simp [Exports] at he

/-- Concrete naming sends the new binder to 2 and old handles to 0 and 1. -/
theorem three_handle_naming :
    outputHandle (none : Option (Fin 2)) = 2 ∧
    outputHandle (some (0 : Fin 2)) = 0 ∧ outputHandle (some (1 : Fin 2)) = 1 := by
  simp only [outputHandle_none,outputHandle_some]
  exact ⟨rfl,rfl,rfl⟩

/-- Mapping the new binder to either previous handle violates freshness. -/
theorem old_handle_alias_blocked (i : Fin 2) :
    outputHandle (none : Option (Fin 2)) ≠ outputHandle (some i) := outputHandle_fresh i

def oldFrame : Frame ({40} : Finset Nat) 1 := ⟨fun _ => .unary .pk (.name 40)⟩

/-- An independently written two-binding frame includes both key and leaked
secret exactly, with no payload replacement in either active substitution. -/
theorem full_active_frame_contents : activeFrame (oldFrame.extend (.name 40)) =
    .par (.active (1 : Fin 2) (.name 40))
      (.par (.active 0 (.unary .pk (.name 40))) (.plain .nil)) := rfl

/-- The actual atomic-output target is structurally the full extended frame
after fresh/last-handle renaming, including the previous public key. -/
theorem secret_output_frame_capture :
    Structural
      ((Extended.par ((activeFrame oldFrame).rename some)
        (capture (groundTerm (.name 40)) (groundAgent Agent.nil))).rename outputHandle)
      (frameProcess (oldFrame.extend (.name 40)) .nil) :=
  frame_output_capture oldFrame (.name 40) .nil

/-- The source-frame representation itself cannot silently redact the leaked
secret at the newly exported handle. -/
theorem redacted_active_frame_differs :
    activeFrame (oldFrame.extend (.name 40)) ≠ activeFrame (oldFrame.extend (.const .bottom)) := by
  intro h
  have he : (Term.name 40 : Term (Fin 2)) = .const .bottom :=
    (Extended.active.inj (Extended.par.inj h).1).2
  cases he

/-- The actual first election publication also has a source bound-output
realization; whole-residual parallel context is handled by the general bridge. -/
theorem honest_publication_derivable (swap : Bool) :
    BoundOutput
      (frameProcess (sourceView SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right .firstReceived)
        (residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical .firstReceived)) 0
      (.par ((activeFrame (sourceView SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right .firstReceived)).rename some)
        (capture (groundTerm (General.ballot SharedTallySPOT.names 0 (General.choice swap SharedTallySPOT.left SharedTallySPOT.right 0).value))
          (groundAgent (residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical .firstPublished)))) :=
  frame_visible_output_derivable _ (residual_publishFirst _ _ _ _ _ _)
end ExplainableCrypto.Helios.Symbolic.SourceAtomicOutputSPOT
