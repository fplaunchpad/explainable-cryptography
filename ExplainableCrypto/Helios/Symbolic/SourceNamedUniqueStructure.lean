import ExplainableCrypto.Helios.Symbolic.SourceNamedUniqueDefinitions

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- Every current structural path preserves exactly the active-definition
condition, even through alpha and the exchange of two restricted variables. -/
theorem Structural.uniqueDefinitions {a b : Named V} (h : Structural a b) :
    a.UniqueDefinitions ↔ b.UniqueDefinitions := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h h' ih ih' => exact ih.trans ih'
  | embed h => exact h.uniqueDefinitions
  | parLeft c h ih =>
    exact and_congr ih (and_congr Iff.rfl (forall_congr' (fun v =>
      not_congr (and_congr (h.exports v) Iff.rfl))))
  | parRight a h ih =>
    exact and_congr Iff.rfl (and_congr ih (forall_congr' (fun v =>
      not_congr (and_congr Iff.rfl (h.exports v)))))
  | newName n h ih => exact ih
  | newVar h ih => exact and_congr ih (h.exports none)
  | embedPar => rfl
  | embedVar => rfl
  | zero => simp [UniqueDefinitions,Exports,Extended.UniqueDefinitions,Extended.Exports]
  | assoc => simp only [UniqueDefinitions,Exports]; aesop
  | comm => simp only [UniqueDefinitions]; aesop
  | nameZero => rfl
  | nameComm => rfl
  | nameVarComm => rfl
  | varComm a =>
    have hn := rename_exports a Extended.swapBinders Extended.swapBinders_involutive.injective (some none)
    have hs := rename_exports a Extended.swapBinders Extended.swapBinders_involutive.injective none
    change (a.UniqueDefinitions ∧ a.Exports none) ∧ a.Exports (some none) ↔
      ((a.rename Extended.swapBinders).UniqueDefinitions ∧ (a.rename Extended.swapBinders).Exports none) ∧
      (a.rename Extended.swapBinders).Exports (some none)
    simp only [Extended.swapBinders] at hn hs
    rw [uniqueDefinitions_rename_iff _ _ Extended.swapBinders_involutive.injective,hn,hs]
    tauto
  | namePar => rfl
  | varPar a b =>
    constructor
    · rintro ⟨ha,⟨hb,hbn⟩,hd⟩
      refine ⟨⟨(uniqueDefinitions_rename_iff a some (Option.some_injective _)).mpr ha,hb,?_⟩,Or.inr hbn⟩
      intro v ⟨hv,hb'⟩
      cases v with
      | none => exact rename_some_no_fresh a hv
      | some v => exact hd v ⟨(rename_exports a some (Option.some_injective _) v).mp hv,hb'⟩
    · rintro ⟨⟨ha,hb,hd⟩,hn | hn⟩
      · exact (rename_some_no_fresh a hn).elim
      · refine ⟨(uniqueDefinitions_rename_iff a some (Option.some_injective _)).mp ha,⟨hb,hn⟩,?_⟩
        intro v ⟨ha',hb'⟩
        exact hd (some v) ⟨(rename_exports a some (Option.some_injective _) v).mpr ha',hb'⟩
  | alphaBase a n m hf => exact (uniqueDefinitions_mapNames_iff a _ _).symm
  | alphaChannel a n m hf => exact (uniqueDefinitions_mapNames_iff a _ _).symm

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
