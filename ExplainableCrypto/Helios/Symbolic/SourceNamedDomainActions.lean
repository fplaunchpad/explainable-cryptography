import ExplainableCrypto.Helios.Symbolic.SourceNamedUniqueStructure

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

theorem Reduction.exports {a b : Named V} (h : Reduction a b) (v : V) :
    a.Exports v ↔ b.Exports v :=
  (a.frameOf_exports v).symm.trans ((h.frameOf.exports v).trans (b.frameOf_exports v))

theorem FreeStep.exports {a b : Named V} {l : Extended.FreeLabel V} (h : FreeStep a l b) (v : V) :
    a.Exports v ↔ b.Exports v :=
  (a.frameOf_exports v).symm.trans ((h.frameOf.exports v).trans (b.frameOf_exports v))

theorem Reduction.uniqueDefinitions {a b : Named V} (h : Reduction a b) :
    a.UniqueDefinitions ↔ b.UniqueDefinitions :=
  a.frameOf_uniqueDefinitions.symm.trans (h.frameOf.uniqueDefinitions.trans b.frameOf_uniqueDefinitions)

theorem FreeStep.uniqueDefinitions {a b : Named V} {l : Extended.FreeLabel V} (h : FreeStep a l b) :
    a.UniqueDefinitions ↔ b.UniqueDefinitions :=
  a.frameOf_uniqueDefinitions.symm.trans (h.frameOf.uniqueDefinitions.trans b.frameOf_uniqueDefinitions)

/-- Reclosure identifies every old exported variable exactly; no source
well-formedness assumption is needed for this domain equality. -/
theorem BoundOutput.old_exports {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) (v : V) : b.Exports (some v) ↔ a.Exports v :=
  (b.frameOf_exports (some v)).symm.trans
    ((h.frameOf_reclose.exports v).trans (a.frameOf_exports v))

/-- The source has unique definitions exactly when the target does and its
fresh output variable is actually defined. This follows from full reclosure. -/
theorem BoundOutput.uniqueDefinitions_iff {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) : a.UniqueDefinitions ↔ b.UniqueDefinitions ∧ b.Exports none := by
  have he := h.frameOf_reclose.uniqueDefinitions
  change (b.frameOf.UniqueDefinitions ∧ b.frameOf.Exports none) ↔ a.frameOf.UniqueDefinitions at he
  exact a.frameOf_uniqueDefinitions.symm.trans
    (he.symm.trans (and_congr b.frameOf_uniqueDefinitions (b.frameOf_exports none)))

theorem BoundOutput.uniqueDefinitions {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) (hu : a.UniqueDefinitions) : b.UniqueDefinitions :=
  (h.uniqueDefinitions_iff.mp hu).1

theorem BoundOutput.new_export {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) (hu : a.UniqueDefinitions) : b.Exports none :=
  (h.uniqueDefinitions_iff.mp hu).2

theorem BoundOutput.all_exports {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) (hu : a.UniqueDefinitions) (ha : ∀ v, a.Exports v) : ∀ v, b.Exports v := by
  intro v
  cases v with
  | none => exact h.new_export hu
  | some v => exact (h.old_exports v).mpr (ha v)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
