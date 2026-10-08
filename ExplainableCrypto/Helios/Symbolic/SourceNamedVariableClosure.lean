import ExplainableCrypto.Helios.Symbolic.SourceNamedDomainActions

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type} {restricted : Finset Nat} {handles : Nat}

/-- All free variable uses, including every active payload position, are in
the supplied scope. Name restriction leaves variable scope unchanged. -/
def VarsIn : {V : Type} → (V → Prop) → Named V → Prop
  | _, s, .embed a => a.VarsIn s
  | _, s, .par a b => a.VarsIn s ∧ b.VarsIn s
  | _, s, .newName _ a => a.VarsIn s
  | _, s, .newVar a => a.VarsIn (binderScope s)

def Closed (a : Named V) : Prop := a.VarsIn a.Exports

/-- Unique definitions and variable closedness only; this is not an assertion
of general acyclicity or satisfaction of every source admissibility condition. -/
def WellFormed (a : Named V) : Prop := a.UniqueDefinitions ∧ a.Closed

theorem varsIn_all (a : Named V) : a.VarsIn (fun _ => True) := by
  induction a with
  | embed a => exact a.varsIn_all
  | par a b ha hb => exact ⟨ha,hb⟩
  | newName n a ih => exact ih
  | newVar a ih =>
    rename_i V'
    have he : binderScope (fun _ : V' => True) = (fun _ => True) := by funext v; cases v <;> rfl
    simpa only [VarsIn,he] using ih

theorem varsIn_mono (a : Named V) {s t : V → Prop} (h : a.VarsIn s) (hs : ∀ v, s v → t v) :
    a.VarsIn t := by
  induction a with
  | embed a => exact a.varsIn_mono h hs
  | par a b ha hb => exact ⟨ha h.1 hs,hb h.2 hs⟩
  | newName n a ih => exact ih h hs
  | newVar a ih =>
    apply ih h
    intro v hv
    cases v with
    | none => trivial
    | some v => exact hs v hv

theorem closed_of_all_exports (a : Named V) (h : ∀ v, a.Exports v) : a.Closed :=
  a.varsIn_mono a.varsIn_all (fun v _ => h v)

theorem closed_empty (a : Named Empty) : a.Closed := closed_of_all_exports a (fun v => v.elim)

theorem Structural.wellFormed_of_all_exports {a b : Named V} (h : Structural a b)
    (hu : a.UniqueDefinitions) (ha : ∀ v, a.Exports v) : b.WellFormed :=
  ⟨h.uniqueDefinitions.mp hu,closed_of_all_exports b (fun v => (h.exports v).mp (ha v))⟩

theorem Reduction.wellFormed_of_all_exports {a b : Named V} (h : Reduction a b)
    (hu : a.UniqueDefinitions) (ha : ∀ v, a.Exports v) : b.WellFormed :=
  ⟨h.uniqueDefinitions.mp hu,closed_of_all_exports b (fun v => (h.exports v).mp (ha v))⟩

theorem FreeStep.wellFormed_of_all_exports {a b : Named V} {l : Extended.FreeLabel V}
    (h : FreeStep a l b) (hu : a.UniqueDefinitions) (ha : ∀ v, a.Exports v) : b.WellFormed :=
  ⟨h.uniqueDefinitions.mp hu,closed_of_all_exports b (fun v => (h.exports v).mp (ha v))⟩

theorem BoundOutput.wellFormed_of_all_exports {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) (hu : a.UniqueDefinitions) (ha : ∀ v, a.Exports v) : b.WellFormed :=
  ⟨h.uniqueDefinitions hu,closed_of_all_exports b (h.all_exports hu ha)⟩

theorem restrictedState_all_exports (hidden : Finset Nat) (p : ScopedState restricted handles) :
    ∀ v, (restrictedState hidden p).Exports v := fun v =>
  (restrictNames_exports _ _ v).mpr (Extended.frameProcess_all_exports p.frame p.body v)

theorem restrictedState_wellFormed (hidden : Finset Nat) (p : ScopedState restricted handles) :
    (restrictedState hidden p).WellFormed :=
  ⟨(restrictNames_uniqueDefinitions _ _).mpr (Extended.frameProcess_wellFormed p.frame p.body).1,
    closed_of_all_exports _ (restrictedState_all_exports hidden p)⟩

/-- Canonical complete-domain representatives supply both premises, so all raw
structural targets are covered even when Rewrite introduces discarded syntax. -/
theorem restrictedState_structural_target (hidden : Finset Nat) (p : ScopedState restricted handles)
    {b : Named (Fin handles)} (h : Structural (restrictedState hidden p) b) : b.WellFormed :=
  h.wellFormed_of_all_exports (restrictedState_wellFormed hidden p).1 (restrictedState_all_exports hidden p)

theorem restrictedState_internal_target (hidden : Finset Nat) (p : ScopedState restricted handles)
    {b : Named (Fin handles)} (h : Reduction (restrictedState hidden p) b) : b.WellFormed :=
  h.wellFormed_of_all_exports (restrictedState_wellFormed hidden p).1 (restrictedState_all_exports hidden p)

theorem restrictedState_free_target (hidden : Finset Nat) (p : ScopedState restricted handles)
    {b : Named (Fin handles)} {l : Extended.FreeLabel (Fin handles)}
    (h : FreeStep (restrictedState hidden p) l b) : b.WellFormed :=
  h.wellFormed_of_all_exports (restrictedState_wellFormed hidden p).1 (restrictedState_all_exports hidden p)

theorem restrictedState_bound_target (hidden : Finset Nat) (p : ScopedState restricted handles)
    {b : Named (Option (Fin handles))} {c : Nat}
    (h : BoundOutput (restrictedState hidden p) c b) : b.WellFormed :=
  h.wellFormed_of_all_exports (restrictedState_wellFormed hidden p).1 (restrictedState_all_exports hidden p)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
