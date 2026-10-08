import ExplainableCrypto.Helios.Symbolic.SourceNamedExports

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V W : Type}

theorem Extended.uniqueDefinitions_mapNames_iff (a : Extended V) (f g : Nat → Nat) :
    (a.mapNames f g).UniqueDefinitions ↔ a.UniqueDefinitions := by
  induction a with
  | plain => rfl
  | active => rfl
  | par a b ha hb =>
    exact and_congr ha (and_congr hb (forall_congr' (fun v =>
      not_congr (and_congr (a.mapNames_exports f g v) (b.mapNames_exports f g v)))))
  | newVar a ih => exact and_congr ih (a.mapNames_exports f g none)

theorem Extended.frameOf_uniqueDefinitions (a : Extended V) :
    a.frameOf.UniqueDefinitions ↔ a.UniqueDefinitions := by
  induction a with
  | plain => rfl
  | active => rfl
  | par a b ha hb =>
    exact and_congr ha (and_congr hb (forall_congr' (fun v =>
      not_congr (and_congr (a.frameOf_exports v) (b.frameOf_exports v)))))
  | newVar a ih => exact and_congr ih (a.frameOf_exports none)

namespace Named

/-- Unique active definitions in the full current named syntax. A restricted
variable has exactly one definition; name binders do not bind variables. -/
def UniqueDefinitions : {V : Type} → Named V → Prop
  | _, .embed a => a.UniqueDefinitions
  | _, .par a b => a.UniqueDefinitions ∧ b.UniqueDefinitions ∧ ∀ v, ¬ (a.Exports v ∧ b.Exports v)
  | _, .newName _ a => a.UniqueDefinitions
  | _, .newVar a => a.UniqueDefinitions ∧ a.Exports none

theorem frameOf_uniqueDefinitions (a : Named V) : a.frameOf.UniqueDefinitions ↔ a.UniqueDefinitions := by
  induction a with
  | embed a => exact a.frameOf_uniqueDefinitions
  | par a b ha hb =>
    exact and_congr ha (and_congr hb (forall_congr' (fun v =>
      not_congr (and_congr (a.frameOf_exports v) (b.frameOf_exports v)))))
  | newName n a ih => exact ih
  | newVar a ih => exact and_congr ih (a.frameOf_exports none)

theorem uniqueDefinitions_mapNames_iff (a : Named V) (f g : Nat → Nat) :
    (a.mapNames f g).UniqueDefinitions ↔ a.UniqueDefinitions := by
  induction a with
  | embed a => exact a.uniqueDefinitions_mapNames_iff f g
  | par a b ha hb =>
    exact and_congr ha (and_congr hb (forall_congr' (fun v =>
      not_congr (and_congr (a.mapNames_exports f g v) (b.mapNames_exports f g v)))))
  | newName n a ih => exact ih
  | newVar a ih => exact and_congr ih (a.mapNames_exports f g none)

theorem uniqueDefinitions_rename_iff (a : Named V) (σ : V → W) (hσ : Function.Injective σ) :
    (a.rename σ).UniqueDefinitions ↔ a.UniqueDefinitions := by
  induction a generalizing W with
  | embed a => exact a.uniqueDefinitions_rename_iff σ hσ
  | newName n a ih => exact ih σ hσ
  | newVar a ih =>
    exact and_congr (ih (Option.map σ) (Option.map_injective hσ))
      (rename_exports a (Option.map σ) (Option.map_injective hσ) none)
  | par a b ha hb =>
    change ((_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _))
    rw [ha σ hσ,hb σ hσ]
    apply and_congr Iff.rfl
    apply and_congr Iff.rfl
    constructor
    · intro hd v ⟨hva,hvb⟩
      exact hd (σ v) ⟨(rename_exports a σ hσ v).mpr hva,(rename_exports b σ hσ v).mpr hvb⟩
    · intro hd w ⟨hwa,hwb⟩
      obtain ⟨v,hv,ha'⟩ := (rename_exports_iff a σ w).mp hwa
      obtain ⟨v',hv',hb'⟩ := (rename_exports_iff b σ w).mp hwb
      have he := hσ (hv.trans hv'.symm)
      subst v'
      exact hd v ⟨ha',hb'⟩

theorem restrictNames_uniqueDefinitions (ns : List SourceName) (a : Named V) :
    (restrictNames ns a).UniqueDefinitions ↔ a.UniqueDefinitions := by
  induction ns <;> simp_all only [restrictNames,List.foldr,UniqueDefinitions]

end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
