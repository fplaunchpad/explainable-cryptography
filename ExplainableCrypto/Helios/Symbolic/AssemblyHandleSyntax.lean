import ExplainableCrypto.Helios.Symbolic.CiphertextGroupingSoundness

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.CiphertextAssembly
variable {n handles : Nat}

/-- Interpret honest selector leaves through the retained original handles.
Constructed leaves retain arbitrary recipes over the whole current frame. -/
def recipeWith (old : Fin 3 → Fin handles) : CiphertextAssembly n handles → Recipe handles
  | .constructed k r p => .ternary .penc k r p
  | .honest i => (Term.var (old i.1.succ)).project i.2.val
  | .mul a b => .binary .mul (a.recipeWith old) (b.recipeWith old)

/-- Select a key from the same assembly. Honest leaves use the retained
public-key handle; constructed keys may have arbitrary public syntax. -/
def keyRecipeWith (old : Fin 3 → Fin handles) : CiphertextAssembly n handles → Recipe handles
  | .constructed k _ _ => k
  | .honest _ => .var (old 0)
  | .mul a _ => a.keyRecipeWith old

end ExplainableCrypto.Helios.Symbolic.Historical.General.CiphertextAssembly
