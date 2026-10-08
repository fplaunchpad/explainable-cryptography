import ExplainableCrypto.Helios.Symbolic.SourceWellFormedStates

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

/-- Internal steps preserve the unique-definition invariant in both directions. -/
theorem Reduction.uniqueDefinitions {a b : Extended V} (h : Reduction a b) :
    a.UniqueDefinitions ↔ b.UniqueDefinitions := by
  induction h with
  | atomComm => rfl
  | thenBranch => rfl
  | elseBranch => rfl
  | parLeft c h ih => exact and_congr ih (and_congr Iff.rfl (forall_congr' (fun v => not_congr (and_congr (h.exports v) Iff.rfl))))
  | parRight a h ih => exact and_congr Iff.rfl (and_congr ih (forall_congr' (fun v => not_congr (and_congr Iff.rfl (h.exports v)))))
  | newVar h ih => exact and_congr ih (h.exports none)
  | congr ha h hb ih => exact ha.uniqueDefinitions.trans (ih.trans hb.uniqueDefinitions)

theorem FreeStep.uniqueDefinitions {a b : Extended V} {l : FreeLabel V} (h : FreeStep a l b) :
    a.UniqueDefinitions ↔ b.UniqueDefinitions := by
  induction h with
  | input => rfl
  | output => rfl
  | scopeInput h ih => exact and_congr ih (h.exports none)
  | scopeOutput h ih => exact and_congr ih (h.exports none)
  | parLeft c h ih => exact and_congr ih (and_congr Iff.rfl (forall_congr' (fun v => not_congr (and_congr (h.exports v) Iff.rfl))))
  | parRight a h ih => exact and_congr Iff.rfl (and_congr ih (forall_congr' (fun v => not_congr (and_congr Iff.rfl (h.exports v)))))
  | congr ha h hb ih => exact ha.uniqueDefinitions.trans (ih.trans hb.uniqueDefinitions)

/-- Exporting a formerly restricted variable preserves its single definition
and cannot collide with an old parallel frame binding. -/
theorem BoundOutput.uniqueDefinitions {a : Extended V} {b : Extended (Option V)} {c : Nat}
    (h : BoundOutput a c b) (hu : a.UniqueDefinitions) : b.UniqueDefinitions := by
  induction h with
  | openAtom h => exact h.uniqueDefinitions.mp hu.1
  | scope h ih =>
    refine ⟨(uniqueDefinitions_rename_iff _ swapBinders swapBinders_involutive.injective).mpr (ih hu.1),?_⟩
    exact (rename_exports _ swapBinders swapBinders_involutive.injective (some none)).mpr ((h.old_exports none).mpr hu.2)
  | parLeft d h ih =>
    refine ⟨ih hu.1,(uniqueDefinitions_rename_iff d some (Option.some_injective _)).mpr hu.2.1,?_⟩
    intro v ⟨hb,hd⟩
    cases v with
    | none => exact rename_some_no_fresh d hd
    | some v => exact hu.2.2 v ⟨(h.old_exports v).mp hb,(rename_exports d some (Option.some_injective _) v).mp hd⟩
  | parRight a h ih =>
    refine ⟨(uniqueDefinitions_rename_iff a some (Option.some_injective _)).mpr hu.1,ih hu.2.1,?_⟩
    intro v ⟨ha,hb⟩
    cases v with
    | none => exact rename_some_no_fresh a ha
    | some v => exact hu.2.2 v ⟨(rename_exports a some (Option.some_injective _) v).mp ha,(h.old_exports v).mp hb⟩
  | congr ha h hb ih => exact hb.uniqueDefinitions.mp (ih (ha.uniqueDefinitions.mp hu))

/-- A well-defined restricted output variable really has an active binding to
export. This fails for unrestricted raw syntax with a missing local definition. -/
theorem BoundOutput.new_export {a : Extended V} {b : Extended (Option V)} {c : Nat}
    (h : BoundOutput a c b) (hu : a.UniqueDefinitions) : b.Exports none := by
  induction h with
  | openAtom h => exact (h.exports none).mp hu.2
  | scope h ih =>
    exact (rename_exports _ swapBinders swapBinders_involutive.injective none).mpr (ih hu.1)
  | parLeft d h ih => exact Or.inl (ih hu.1)
  | parRight a h ih => exact Or.inr (ih hu.2.1)
  | congr ha h hb ih => exact (hb.exports none).mp (ih (ha.uniqueDefinitions.mp hu))

/-- Actual frame domains cover every available free variable. Bound output
extends that property by exactly its fresh exported variable. -/
theorem BoundOutput.all_exports {a : Extended V} {b : Extended (Option V)} {c : Nat}
    (h : BoundOutput a c b) (hu : a.UniqueDefinitions) (ha : ∀ v, a.Exports v) : ∀ v, b.Exports v := by
  intro v
  cases v with
  | none => exact h.new_export hu
  | some v => exact (h.old_exports v).mpr (ha v)

/-- Covering the whole variable domain is stronger than arbitrary syntactic
closedness and is preserved by raw structural rules, including EqE Rewrite. -/
theorem Structural.wellFormed_of_all_exports {a b : Extended V} (h : Structural a b)
    (hu : a.UniqueDefinitions) (ha : ∀ v, a.Exports v) : b.WellFormed :=
  ⟨h.uniqueDefinitions.mp hu,closed_of_all_exports b (fun v => (h.exports v).mp (ha v))⟩

theorem Reduction.wellFormed_of_all_exports {a b : Extended V} (h : Reduction a b)
    (hu : a.UniqueDefinitions) (ha : ∀ v, a.Exports v) : b.WellFormed :=
  ⟨h.uniqueDefinitions.mp hu,closed_of_all_exports b (fun v => (h.exports v).mp (ha v))⟩

theorem FreeStep.wellFormed_of_all_exports {a b : Extended V} {l : FreeLabel V} (h : FreeStep a l b)
    (hu : a.UniqueDefinitions) (ha : ∀ v, a.Exports v) : b.WellFormed :=
  ⟨h.uniqueDefinitions.mp hu,closed_of_all_exports b (fun v => (h.exports v).mp (ha v))⟩

theorem BoundOutput.wellFormed_of_all_exports {a : Extended V} {b : Extended (Option V)} {c : Nat}
    (h : BoundOutput a c b) (hu : a.UniqueDefinitions) (ha : ∀ v, a.Exports v) : b.WellFormed :=
  ⟨h.uniqueDefinitions hu,closed_of_all_exports b (h.all_exports hu ha)⟩

variable {restricted : Finset Nat} {handles : Nat}

theorem frameProcess_all_exports (φ : Frame restricted handles) (p : Agent Empty) :
    ∀ v, (frameProcess φ p).Exports v := fun v => Or.inl (activeFrame_exports φ v)

/-- No conditional closedness premise is left for arbitrary structural targets
of the actual canonical frame/process representation. -/
theorem frameProcess_structural_target (φ : Frame restricted handles) (p : Agent Empty)
    {q : Extended (Fin handles)} (h : Structural (frameProcess φ p) q) : q.WellFormed :=
  h.wellFormed_of_all_exports (frameProcess_wellFormed φ p).1 (frameProcess_all_exports φ p)

theorem frameProcess_internal_target (φ : Frame restricted handles) (p : Agent Empty)
    {q : Extended (Fin handles)} (h : Reduction (frameProcess φ p) q) : q.WellFormed :=
  h.wellFormed_of_all_exports (frameProcess_wellFormed φ p).1 (frameProcess_all_exports φ p)

theorem frameProcess_free_target (φ : Frame restricted handles) (p : Agent Empty)
    {q : Extended (Fin handles)} {l : FreeLabel (Fin handles)} (h : FreeStep (frameProcess φ p) l q) : q.WellFormed :=
  h.wellFormed_of_all_exports (frameProcess_wellFormed φ p).1 (frameProcess_all_exports φ p)

theorem frameProcess_bound_target (φ : Frame restricted handles) (p : Agent Empty)
    {q : Extended (Option (Fin handles))} {c : Nat} (h : BoundOutput (frameProcess φ p) c q) : q.WellFormed :=
  h.wellFormed_of_all_exports (frameProcess_wellFormed φ p).1 (frameProcess_all_exports φ p)
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
