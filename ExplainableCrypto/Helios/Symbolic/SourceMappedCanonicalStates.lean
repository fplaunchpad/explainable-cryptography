import ExplainableCrypto.Helios.Symbolic.SourceElectionJointVisible

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
namespace Named
variable {restricted : Finset Nat} {handles : Nat}

/-- A complete canonical state in explicit shared base/channel coordinates.
Both restriction policies and every frame/body occurrence move together. -/
noncomputable def mappedState (hidden : Finset Nat) (s : ScopedState restricted handles)
    (e k : Nat ≃ Nat) : Named (Fin handles) := restrictedState (hidden.image k) (s.mapNames e k)

theorem mappedState_identity (hidden : Finset Nat) (s : ScopedState restricted handles) :
    mappedState hidden s (Equiv.refl Nat) (Equiv.refl Nat) = restrictedState hidden s := by
  simp only [mappedState,restrictedState,ScopedState.mapNames,← Extended.frameProcess_mapNames,
    Equiv.coe_refl,Finset.image_id,Extended.mapNames_id]

/-- Composition is equality of the actual Named processes, avoiding a phantom
policy cast between the intermediate ScopedState types. -/
theorem mappedState_comp (hidden : Finset Nat) (s : ScopedState restricted handles)
    (e k f l : Nat ≃ Nat) :
    mappedState (hidden.image k) (s.mapNames e k) f l = mappedState hidden s (e.trans f) (k.trans l) := by
  simp only [mappedState,restrictedState,ScopedState.mapNames,← Extended.frameProcess_mapNames,
    Extended.mapNames_comp,Finset.image_image,Equiv.coe_trans]

end Named

namespace Agent
variable {restricted : Finset Nat} {handles : Nat}

theorem Visible.input_inverse_frame {p q : Agent Empty} {φ : Frame restricted handles}
    {c : Nat} {r : Recipe handles} (e k : Nat ≃ Nat)
    (h : Visible (p.mapNames e k) (.input c ((φ.mapNames e).eval r)) q) :
    Visible p (.input (k.symm c) (φ.eval (r.mapNames e.symm))) (q.mapNames e.symm k.symm) := by
  have hv : ((φ.mapNames e).eval r).mapNames e.symm = φ.eval (r.mapNames e.symm) := by
    rw [Frame.eval_mapNames_inverse,Term.mapNames_inverse]
  simpa only [Agent.mapNames_inverse,PayloadEvent.mapNames,hv] using h.mapNames e.symm k.symm

theorem Visible.input_forward_frame {p q : Agent Empty} {φ : Frame restricted handles}
    {c : Nat} {r : Recipe handles} (e k : Nat ≃ Nat)
    (h : Visible p (.input (k.symm c) (φ.eval (r.mapNames e.symm))) q) :
    Visible (p.mapNames e k) (.input c ((φ.mapNames e).eval r)) (q.mapNames e k) := by
  simpa only [PayloadEvent.mapNames,Equiv.apply_symm_apply,← Frame.eval_mapNames_inverse] using h.mapNames e k

end Agent
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
