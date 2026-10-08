import ExplainableCrypto.Helios.Symbolic.SourceExtendedInternal
import ExplainableCrypto.Helios.Symbolic.SourceVisibleCorrespondenceSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceActiveBindingSPOT
open Historical General Source

/-- A compound message that itself refers to a pre-existing free variable. -/
def message : Term (Fin 1) := .binary .pair (.name 40) (.var 0)

/-- One local let variable, one subsequent input variable, and one old variable
are all used in distinct positions of the same eventual output. -/
def nested : Agent (Option (Fin 1)) := .input 6
  (.output 7 (.binary .pair (.var (some none))
    (.binary .pair (.var none) (.var (some (some 0))))) .nil)

def expected : Agent (Fin 1) := .input 6
  (.output 7 (.binary .pair (.binary .pair (.name 40) (.var (some 0)))
    (.binary .pair (.var none) (.var (some 0)))) .nil)

/-- The independently written result retains all three variable roles. -/
theorem nested_binding_exact : nested.bind message = expected := rfl

/-- Source Alias/Subst/scope rules eliminate the local active let to that
explicit continuation, without evaluating or capturing the old variable. -/
theorem nested_active_let_eliminates :
    Extended.Structural (Extended.letTerm message nested) (.plain expected) :=
  Extended.let_eliminate message nested

/-- Moving the let value into the newer input slot is a different process. -/
theorem captured_input_mutant_rejected :
    nested.bind message ≠ (.input 6 (.output 7
      (.binary .pair (.var none) (.binary .pair (.var none) (.var (some 0)))) .nil) : Agent (Fin 1)) := by
  intro h
  simp [nested,message,Agent.bind,Agent.subst,liftSubst,inputSubst,Term.subst] at h

/-- The same nested continuation is reached by compound-message communication,
using the derived atomic/active rule rather than direct CoreStep.comm. -/
theorem compound_atomic_communication :
    Extended.Reduction (.plain (.par (.output 5 message (.output 8 (.var 0) .nil)) (.input 5 nested)))
      (.plain (.par (.output 8 (.var 0) .nil) expected)) :=
  Extended.message_communication 5 message _ nested

/-- Restriction makes an unused fresh alias removable. -/
theorem restricted_alias_eliminates :
    Extended.Structural (Extended.newVar (.active none (shiftTerm message))) (.plain .nil) :=
  .alias message

/-- Its exported counterpart cannot be discarded, even when unused. -/
theorem exported_alias_not_discarded :
    ¬ Extended.Structural (.active (0 : Fin 1) message) (.plain .nil) :=
  Extended.active_not_plain 0 message .nil

/-- An internal reduction cannot consume that public frame binding either. -/
theorem exported_alias_not_consumed :
    ¬ Extended.Reduction (.active (0 : Fin 1) message) (.plain .nil) :=
  Extended.active_no_plain_reduction 0 message .nil

/-- Fresh scope extrusion preserves the already exported old variable. -/
theorem extrusion_keeps_export :
    Extended.Structural
      (.par (.active (0 : Fin 1) message) (.newVar (.active none (shiftTerm message))))
      (.newVar (.par (.active (some 0) (shiftTerm message)) (.active none (shiftTerm message)))) ∧
    (Extended.newVar (.par (.active (some (0 : Fin 1)) (shiftTerm message))
      (.active none (shiftTerm message)))).Exports 0 := by
  exact ⟨.newPar _ _,Or.inl rfl⟩

/-- The actual first private honest handshake has an atomic/active derivation,
with the other voter and trustee retained in parallel. -/
theorem honest_handshake_derivable (swap : Bool) :
    Extended.Reduction
      (.plain (residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical .start))
      (.plain (residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical .firstReceived)) :=
  Extended.residual_internal_derivable _ _ _ _ _ _ .receiveFirst

/-- A replay's failed guard still takes the rejecting branch, retaining the
waiting trustee. The derived source rule does not turn rejection into acceptance. -/
theorem replay_rejection_derivable (swap : Bool) :
    Extended.Reduction
      (.plain (residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical
        (.check [] (.var 1))))
      (.plain (residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical
        (.rejected []))) := by
  apply Extended.residual_internal_derivable
  apply Process.Step.reject
  intro h
  have hs : (SharedTallySPOT.world swap).AcceptsSequence 0 (.var 0) honestBoardRecipes [.var 1] :=
    ⟨h,True.intro⟩
  exact SharedTallySPOT.honest_replay_rejected swap hs
end ExplainableCrypto.Helios.Symbolic.SourceActiveBindingSPOT
