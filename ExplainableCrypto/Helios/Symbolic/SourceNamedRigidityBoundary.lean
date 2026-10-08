import ExplainableCrypto.Helios.Symbolic.SourceStructuralOpeningComparison
import ExplainableCrypto.Helios.Symbolic.SourceRigidityBoundary
import ExplainableCrypto.Helios.Symbolic.SourceBoundRigidity

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type} {restricted : Finset Nat} {handles : Nat}

/-- Name-scoped structural detours between embedded endpoints introduce no
extra body equivalence beyond original Extended paths and variable commutation. -/
theorem Structural.binder_of_embeds {a b : Extended V} (h : Structural (.embed a) (.embed b)) :
    a.BinderStructural b := by
  have ho : Opens (.embed a) NameAssignment.literal [] a := by
    simpa only [show NameAssignment.literal.base = id from rfl,
      show NameAssignment.literal.channel = id from rfl,Extended.mapNames_id] using Opens.embed a NameAssignment.literal
  obtain ⟨ms,q,hq,_,he⟩ := h.transport_binder_opening NameAssignment.literal [] a ∅ ho (by simp)
  cases hq
  simpa only [show NameAssignment.literal.base = id from rfl,
    show NameAssignment.literal.channel = id from rfl,Extended.mapNames_id] using he

theorem structural_embeds_iff_binder (a b : Extended V) :
    Structural (.embed a) (.embed b) ↔ a.BinderStructural b :=
  ⟨Structural.binder_of_embeds,Extended.BinderStructural.named⟩

/-- The full Named source calculus preserves local rigidity between embedded
endpoints, including alpha, name extrusion and variable-binder exchanges. -/
theorem Structural.rigid_embeds {a b : Extended V} (h : Structural (.embed a) (.embed b))
    (env : V → Ground) : a.Rigid env ↔ b.Rigid env := h.binder_of_embeds.rigid env

/-- The earlier cyclic counterexample remains separated in the complete
Named structural calculus, not only in its Extended fragment. -/
theorem unconstrained_local_not_structural :
    ¬ Structural (.embed (.newVar (.active none (.var none)) : Extended V)) (.embed (.plain .nil)) := by
  intro h
  exact Extended.unconstrained_local_not_rigid (fun _ => .name 42) ((h.rigid_embeds _).mpr True.intro)

/-- Complete canonical frames and bodies do not repair the cyclic semantic
pair, even when all Named structural rules are available along the path. -/
theorem frame_with_unconstrained_local_not_structural (φ : Frame restricted handles) (p : Agent Empty) :
    ¬ Structural (.embed (.par (Extended.frameProcess φ p) (.newVar (.active none (.var none)))))
      (.embed (Extended.frameProcess φ p)) := by
  intro h
  have hr := (h.rigid_embeds φ.value).mpr (Extended.frameProcess_rigid φ p φ.value)
  have hs : (Extended.frameProcess φ p).Satisfies φ.value := by
    change (Extended.activeFrame φ).Satisfies φ.value ∧ True
    exact ⟨(Extended.activeFrame_satisfies_iff φ φ.value).mpr (fun _ => .refl _),True.intro⟩
  exact Extended.unconstrained_local_not_rigid φ.value (hr hs ⟨.name 40,.refl _⟩).2

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
