import ExplainableCrypto.Helios.Symbolic.SourceExtendedFrameProjection

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V W : Type}

/-- Frame extraction keeps name binders, including private keys, and every
active value. It does not evaluate or redact any term. -/
def frameOf : {V : Type} → Named V → Named V
  | _, .embed a => .embed a.frameOf
  | _, .par a b => .par a.frameOf b.frameOf
  | _, .newName n a => .newName n a.frameOf
  | _, .newVar a => .newVar a.frameOf

theorem frameOf_idempotent (a : Named V) : a.frameOf.frameOf = a.frameOf := by
  induction a <;> simp_all only [frameOf,Extended.frameOf_idempotent]

theorem frameOf_rename (a : Named V) (σ : V → W) :
    (a.rename σ).frameOf = a.frameOf.rename σ := by
  induction a generalizing W <;> simp_all only [rename,frameOf,Extended.frameOf_rename]

theorem frameOf_mapNames (a : Named V) (f g : Nat → Nat) :
    (a.mapNames f g).frameOf = a.frameOf.mapNames f g := by
  induction a <;> simp_all only [mapNames,frameOf,Extended.frameOf_mapNames]

theorem frameOf_freeNames (a : Named V) : a.frameOf.freeNames ⊆ a.freeNames := by
  induction a with
  | embed a => exact a.frameOf_nameSupport
  | par a b ha hb => exact Finset.union_subset_union ha hb
  | newName n a ih => exact Finset.erase_subset_erase n ih
  | newVar a ih => exact ih

theorem frameOf_allNames (a : Named V) : a.frameOf.allNames ⊆ a.allNames := by
  induction a with
  | embed a => exact a.frameOf_nameSupport
  | par a b ha hb => exact Finset.union_subset_union ha hb
  | newName n a ih => exact Finset.insert_subset_insert n ih
  | newVar a ih => exact ih

theorem frameOf_restrictNames (ns : List SourceName) (a : Named V) :
    (restrictNames ns a).frameOf = restrictNames ns a.frameOf := by
  induction ns <;> simp_all only [restrictNames,List.foldr,frameOf]

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
