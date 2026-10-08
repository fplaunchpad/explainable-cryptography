import ExplainableCrypto.Helios.Symbolic.SourceVariableScope

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V W : Type}

/-- At most one active definition of each variable; every variable restriction
has its own definition. Input binders in plain processes need no active binding. -/
def UniqueDefinitions : {V : Type} → Extended V → Prop
  | _, .plain _ => True
  | _, .active _ _ => True
  | _, .par a b => a.UniqueDefinitions ∧ b.UniqueDefinitions ∧ ∀ v, ¬ (a.Exports v ∧ b.Exports v)
  | _, .newVar a => a.UniqueDefinitions ∧ a.Exports none

/-- Renaming produces exactly the image of the exported variable domain. -/
theorem rename_exports_iff (a : Extended V) (f : V → W) (w : W) :
    (a.rename f).Exports w ↔ ∃ v, f v=w ∧ a.Exports v := by
  induction a generalizing W with
  | plain p => simp [rename,Exports]
  | active x m =>
    constructor
    · intro h
      exact ⟨x,h.symm,rfl⟩
    · rintro ⟨v,hf,rfl⟩
      exact hf.symm
  | par a b ha hb =>
    change ((a.rename f).Exports w ∨ (b.rename f).Exports w) ↔ _
    rw [ha,hb]
    constructor
    · rintro (⟨v,hv,he⟩ | ⟨v,hv,he⟩)
      · exact ⟨v,hv,Or.inl he⟩
      · exact ⟨v,hv,Or.inr he⟩
    · rintro ⟨v,hv,he | he⟩
      · exact Or.inl ⟨v,hv,he⟩
      · exact Or.inr ⟨v,hv,he⟩
  | newVar a ha =>
    change (a.rename (Option.map f)).Exports (some w) ↔ _
    rw [ha]
    constructor
    · rintro ⟨v,hv,he⟩
      cases v with
      | none => cases hv
      | some v => exact ⟨v,Option.some.inj hv,he⟩
    · rintro ⟨v,hv,he⟩
      exact ⟨some v,congrArg some hv,he⟩

/-- Shifting the old context introduces no definition of the fresh binder. -/
theorem rename_some_no_fresh (a : Extended V) : ¬ (a.rename some).Exports none := by
  rw [rename_exports_iff]
  rintro ⟨v,hv,_⟩
  cases hv

/-- Injective renaming neither merges nor removes active definitions. -/
theorem uniqueDefinitions_rename_iff (a : Extended V) (f : V → W) (hf : Function.Injective f) :
    (a.rename f).UniqueDefinitions ↔ a.UniqueDefinitions := by
  induction a generalizing W with
  | plain => rfl
  | active => rfl
  | newVar a ha =>
    exact and_congr (ha (Option.map f) (Option.map_injective hf))
      (rename_exports a (Option.map f) (Option.map_injective hf) none)
  | par a b ha hb =>
    change ((_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _))
    rw [ha f hf,hb f hf]
    apply and_congr Iff.rfl
    apply and_congr Iff.rfl
    constructor
    · intro hd v ⟨hva,hvb⟩
      exact hd (f v) ⟨(rename_exports a f hf v).mpr hva,(rename_exports b f hf v).mpr hvb⟩
    · intro hd w ⟨hwa,hwb⟩
      obtain ⟨v,hv,ha'⟩ := (rename_exports_iff a f w).mp hwa
      obtain ⟨v',hv',hb'⟩ := (rename_exports_iff b f w).mp hwb
      have he := hf (hv.trans hv'.symm)
      subst v'
      exact hd v ⟨ha',hb'⟩

/-- All structural rules of the variable/active fragment preserve uniqueness
and the required definition under each variable restriction. -/
theorem Structural.uniqueDefinitions {a b : Extended V} (h : Structural a b) :
    a.UniqueDefinitions ↔ b.UniqueDefinitions := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | plainPar => simp [UniqueDefinitions,Exports]
  | zero => simp [UniqueDefinitions,Exports]
  | comm a b =>
    simp only [UniqueDefinitions]
    aesop
  | assoc a b c =>
    simp only [UniqueDefinitions,Exports]
    aesop
  | parLeft c h ih =>
    exact and_congr ih (and_congr Iff.rfl (forall_congr' (fun v => not_congr (and_congr (h.exports v) Iff.rfl))))
  | parRight a h ih =>
    simp only [UniqueDefinitions]
    exact and_congr Iff.rfl (and_congr ih (forall_congr' (fun v => not_congr (and_congr Iff.rfl (h.exports v)))))
  | newVar h ih => exact and_congr ih (h.exports none)
  | «alias» => simp [UniqueDefinitions,Exports]
  | substPlain => simp [UniqueDefinitions,Exports]
  | substActive => rfl
  | rewrite => rfl
  | newPar a b =>
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
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
