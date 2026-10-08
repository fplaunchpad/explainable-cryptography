import ExplainableCrypto.Helios.Symbolic.SourceCanonicalFrameProjection
import ExplainableCrypto.Helios.Symbolic.SourceWellFormedPreservation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V W : Type}

theorem Extended.mapNames_exports (a : Extended V) (f g : Nat → Nat) (v : V) :
    (a.mapNames f g).Exports v ↔ a.Exports v := by
  induction a with
  | plain => rfl
  | active => rfl
  | par a b ha hb => exact or_congr (ha v) (hb v)
  | newVar a ih => exact ih (some v)

namespace Named

/-- The frame domain of a general named process. Name restriction never
binds a variable; variable restriction hides precisely None. -/
def Exports : {V : Type} → Named V → V → Prop
  | _, .embed a, v => a.Exports v
  | _, .par a b, v => a.Exports v ∨ b.Exports v
  | _, .newName _ a, v => a.Exports v
  | _, .newVar a, v => a.Exports (some v)

theorem frameOf_exports (a : Named V) (v : V) : a.frameOf.Exports v ↔ a.Exports v := by
  induction a with
  | embed a => exact a.frameOf_exports v
  | par a b ha hb => exact or_congr (ha v) (hb v)
  | newName n a ih => exact ih v
  | newVar a ih => exact ih (some v)

theorem mapNames_exports (a : Named V) (f g : Nat → Nat) (v : V) :
    (a.mapNames f g).Exports v ↔ a.Exports v := by
  induction a with
  | embed a => exact a.mapNames_exports f g v
  | par a b ha hb => exact or_congr (ha v) (hb v)
  | newName n a ih => exact ih v
  | newVar a ih => exact ih (some v)

theorem rename_exports_iff (a : Named V) (σ : V → W) (w : W) :
    (a.rename σ).Exports w ↔ ∃ v, σ v = w ∧ a.Exports v := by
  induction a generalizing W with
  | embed a => exact a.rename_exports_iff σ w
  | newName n a ih => exact ih σ w
  | par a b ha hb =>
    change ((a.rename σ).Exports w ∨ (b.rename σ).Exports w) ↔ _
    rw [ha,hb]
    constructor
    · rintro (⟨v,hv,he⟩ | ⟨v,hv,he⟩)
      · exact ⟨v,hv,Or.inl he⟩
      · exact ⟨v,hv,Or.inr he⟩
    · rintro ⟨v,hv,he | he⟩
      · exact Or.inl ⟨v,hv,he⟩
      · exact Or.inr ⟨v,hv,he⟩
  | newVar a ih =>
    change (a.rename (Option.map σ)).Exports (some w) ↔ _
    rw [ih]
    constructor
    · rintro ⟨v,hv,he⟩
      cases v with
      | none => cases hv
      | some v => exact ⟨v,Option.some.inj hv,he⟩
    · rintro ⟨v,hv,he⟩
      exact ⟨some v,congrArg some hv,he⟩

theorem rename_exports (a : Named V) (σ : V → W) (hσ : Function.Injective σ) (v : V) :
    (a.rename σ).Exports (σ v) ↔ a.Exports v := by
  rw [rename_exports_iff]
  constructor
  · rintro ⟨w,hw,he⟩
    exact hσ hw ▸ he
  · exact fun h => ⟨v,rfl,h⟩

theorem rename_some_no_fresh (a : Named V) : ¬ (a.rename some).Exports none := by
  rw [rename_exports_iff]
  rintro ⟨v,hv,_⟩
  cases hv

theorem restrictNames_exports (ns : List SourceName) (a : Named V) (v : V) :
    (restrictNames ns a).Exports v ↔ a.Exports v := by
  induction ns <;> simp_all only [restrictNames,List.foldr,Exports]

/-- Every existing structural constructor preserves the exported variable
domain, including alpha, variable exchange and both forms of extrusion. -/
theorem Structural.exports {a b : Named V} (h : Structural a b) (v : V) :
    a.Exports v ↔ b.Exports v := by
  induction h with
  | refl => rfl
  | symm h ih => exact (ih v).symm
  | trans h h' ih ih' => exact (ih v).trans (ih' v)
  | embed h => exact h.exports v
  | parLeft c h ih => exact or_congr (ih v) Iff.rfl
  | parRight a h ih => exact or_congr Iff.rfl (ih v)
  | newName n h ih => exact ih v
  | newVar h ih => exact ih (some v)
  | embedPar => rfl
  | embedVar => rfl
  | zero => simp [Exports,Extended.Exports]
  | assoc => simp [Exports,or_assoc]
  | comm => simp [Exports,or_comm]
  | nameZero => rfl
  | nameComm => rfl
  | nameVarComm => rfl
  | varComm a => exact (rename_exports a Extended.swapBinders Extended.swapBinders_involutive.injective (some (some v))).symm
  | namePar => rfl
  | varPar a b => exact or_congr (rename_exports a some (Option.some_injective _) v).symm Iff.rfl
  | alphaBase a n m hf => exact (mapNames_exports a _ _ v).symm
  | alphaChannel a n m hf => exact (mapNames_exports a _ _ v).symm

end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
