import ExplainableCrypto.Helios.Symbolic.SourceLocalRigidity

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type} {restricted : Finset Nat} {handles : Nat}

/-- Internal steps preserve local rigidity because their complete frames are
Structurally related, including all enclosing variable binders. -/
theorem Reduction.rigid {a b : Extended V} (h : Reduction a b) (env : V → Ground) :
    a.Rigid env ↔ b.Rigid env :=
  (rigid_frameOf a env).symm.trans ((h.frameOf.rigid env).trans (rigid_frameOf b env))

/-- Both kinds of free labels preserve the same old local-solution property. -/
theorem FreeStep.rigid {a b : Extended V} {l : FreeLabel V} (h : FreeStep a l b) (env : V → Ground) :
    a.Rigid env ↔ b.Rigid env :=
  (rigid_frameOf a env).symm.trans ((h.frameOf.rigid env).trans (rigid_frameOf b env))

theorem frameEntries_rigid (h : Nat) (vars : Fin h → V) (values : Fin h → Ground) (env : V → Ground) :
    (frameEntries h vars values).Rigid env := by
  induction h with
  | zero => trivial
  | succ h ih => exact fun _ _ => ⟨True.intro,ih _ _⟩

theorem activeFrame_rigid (φ : Frame restricted handles) (env : Fin handles → Ground) :
    (activeFrame φ).Rigid env := frameEntries_rigid handles id φ.value env

/-- Canonical frame/process states have no unresolved local variable choices. -/
theorem frameProcess_rigid (φ : Frame restricted handles) (p : Agent Empty) (env : Fin handles → Ground) :
    (frameProcess φ p).Rigid env := fun _ _ => ⟨activeFrame_rigid φ env,True.intro⟩

/-- Any actual Extended normalization to a canonical state must preserve the
extra local-solution information that SameRealizations alone can forget. -/
theorem Structural.rigid_of_frame_target {a : Extended (Fin handles)}
    (φ : Frame restricted handles) (p : Agent Empty) (h : Structural a (frameProcess φ p))
    (env : Fin handles → Ground) : a.Rigid env :=
  (h.rigid env).mpr (frameProcess_rigid φ p env)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
