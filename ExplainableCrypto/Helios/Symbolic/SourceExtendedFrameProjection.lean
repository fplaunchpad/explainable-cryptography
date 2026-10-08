import ExplainableCrypto.Helios.Symbolic.SourceNamedVariableRename

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V W : Type}

/-- Applied-pi frame extraction retains all active payloads and variable
restrictions, replacing each plain process with Nil. -/
def frameOf : {V : Type} → Extended V → Extended V
  | _, .plain _ => .plain .nil
  | _, .active x m => .active x m
  | _, .par a b => .par a.frameOf b.frameOf
  | _, .newVar a => .newVar a.frameOf

theorem frameOf_idempotent (a : Extended V) : a.frameOf.frameOf = a.frameOf := by
  induction a <;> simp_all only [frameOf]

theorem frameOf_rename (a : Extended V) (σ : V → W) :
    (a.rename σ).frameOf = a.frameOf.rename σ := by
  induction a generalizing W <;> simp_all only [rename,frameOf,Agent.subst]

theorem frameOf_mapNames (a : Extended V) (f g : Nat → Nat) :
    (a.mapNames f g).frameOf = a.frameOf.mapNames f g := by
  induction a <;> simp_all only [mapNames,frameOf,Agent.mapNames]

theorem frameOf_exports (a : Extended V) (v : V) : a.frameOf.Exports v ↔ a.Exports v := by
  induction a with
  | plain => rfl
  | active => rfl
  | par a b ha hb => exact or_congr (ha v) (hb v)
  | newVar a ih => exact ih (some v)

theorem frameOf_nameSupport (a : Extended V) : a.frameOf.nameSupport ⊆ a.nameSupport := by
  induction a with
  | plain => exact Finset.empty_subset _
  | active => exact Finset.Subset.refl _
  | par a b ha hb => exact Finset.union_subset_union ha hb
  | newVar a ih => exact ih

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
