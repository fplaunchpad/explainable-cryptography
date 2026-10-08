import ExplainableCrypto.Helios.Symbolic.SourceStructuralVariableRename

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V W U : Type}

theorem rename_comp (a : Named V) (σ : V → W) (τ : W → U) :
    (a.rename σ).rename τ = a.rename (τ ∘ σ) := by
  induction a generalizing W U with
  | embed a => simp only [Named.rename,Extended.rename_comp]
  | par a b ha hb => simp only [Named.rename,ha,hb]
  | newName n a ih => simp only [Named.rename,ih]
  | newVar a ih =>
    simp only [Named.rename,ih]
    congr 2
    funext v
    cases v <;> rfl

theorem freeNames_rename (a : Named V) (σ : V → W) : (a.rename σ).freeNames = a.freeNames := by
  induction a generalizing W with
  | embed a => exact a.nameSupport_rename σ
  | par a b ha hb => simp only [Named.rename,freeNames,ha,hb]
  | newName n a ih => simp only [Named.rename,freeNames,ih]
  | newVar a ih => exact ih (Option.map σ)

theorem allNames_rename (a : Named V) (σ : V → W) : (a.rename σ).allNames = a.allNames := by
  induction a generalizing W with
  | embed a => exact a.nameSupport_rename σ
  | par a b ha hb => simp only [Named.rename,allNames,ha,hb]
  | newName n a ih => simp only [Named.rename,allNames,ih]
  | newVar a ih => exact ih (Option.map σ)

theorem rename_swapBinders (a : Named (Option (Option V))) (σ : V → W) :
    (a.rename Extended.swapBinders).rename (Option.map (Option.map σ)) =
      (a.rename (Option.map (Option.map σ))).rename Extended.swapBinders := by
  simp only [rename_comp]
  congr 1
  funext v
  cases v with
  | none => rfl
  | some v => cases v <;> rfl

/-- All Named structural paths transport under injective variable renaming,
including alpha, fresh name extrusion and the two-variable exchange. -/
theorem Structural.rename {a b : Named V} (h : Structural a b) (σ : V → W)
    (hσ : Function.Injective σ) : Structural (a.rename σ) (b.rename σ) := by
  induction h generalizing W with
  | refl => exact .refl _
  | symm h ih => exact (ih σ hσ).symm
  | trans h h' ih ih' => exact (ih σ hσ).trans (ih' σ hσ)
  | embed h => exact .embed (h.rename σ hσ)
  | parLeft c h ih => exact .parLeft _ (ih σ hσ)
  | parRight a h ih => exact .parRight _ (ih σ hσ)
  | newName n h ih => exact .newName n (ih σ hσ)
  | newVar h ih => exact .newVar (ih (Option.map σ) (option_map_injective σ hσ))
  | embedPar => exact .embedPar _ _
  | embedVar => exact .embedVar _
  | zero => exact .zero _
  | assoc => exact .assoc _ _ _
  | comm => exact .comm _ _
  | nameZero => exact .nameZero _
  | nameComm => exact .nameComm _ _ _
  | nameVarComm => exact .nameVarComm _ _
  | varComm a =>
    simpa only [Named.rename,rename_swapBinders] using
      Structural.varComm (a.rename (Option.map (Option.map σ)))
  | namePar a n b hf => exact .namePar _ _ _ (by simpa only [freeNames_rename] using hf)
  | varPar a b =>
    simpa only [Named.rename,rename_comp,Function.comp_def,Option.map_some] using
      Structural.varPar (a.rename σ) (b.rename (Option.map σ))
  | alphaBase a n m hf =>
    simpa only [Named.rename,mapNames_rename] using
      Structural.alphaBase (a.rename σ) n m (by simpa only [allNames_rename] using hf)
  | alphaChannel a n m hf =>
    simpa only [Named.rename,mapNames_rename] using
      Structural.alphaChannel (a.rename σ) n m (by simpa only [allNames_rename] using hf)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
