import ExplainableCrypto.Helios.Symbolic.SourceStructuralVariableRename
import ExplainableCrypto.Helios.Symbolic.SourceFrameStructure

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V W : Type}

/-- Substitute a free variable in all payloads and plain processes, leaving
active domains fixed. Under a variable restriction, the provider variable and
its full payload shift past the fresh None. -/
noncomputable def substFree : {V : Type} → V → Term V → Extended V → Extended V
  | _, x, m, .plain p => .plain (p.subst (replaceVar x m))
  | _, x, m, .active y n => .active y (n.subst (replaceVar x m))
  | _, x, m, .par a b => .par (a.substFree x m) (b.substFree x m)
  | _, x, m, .newVar a => .newVar (a.substFree (some x) (shiftTerm m))

theorem substFree_exports (a : Extended V) (x : V) (m : Term V) (v : V) :
    (a.substFree x m).Exports v ↔ a.Exports v := by
  induction a with
  | plain => rfl
  | active => rfl
  | par a b ha hb => exact or_congr (ha x m v) (hb x m v)
  | newVar a ih => exact ih (some x) (shiftTerm m) (some v)

theorem substFree_uniqueDefinitions (a : Extended V) (x : V) (m : Term V) :
    (a.substFree x m).UniqueDefinitions ↔ a.UniqueDefinitions := by
  induction a with
  | plain => rfl
  | active => rfl
  | par a b ha hb => exact and_congr (ha x m) (and_congr (hb x m)
      (forall_congr' (fun v => not_congr (and_congr (a.substFree_exports x m v) (b.substFree_exports x m v)))))
  | newVar a ih => exact and_congr (ih (some x) (shiftTerm m)) (a.substFree_exports (some x) (shiftTerm m) none)

theorem substFree_rename (a : Extended V) (x : V) (m : Term V) (σ : V → W) (hσ : Function.Injective σ) :
    (a.substFree x m).rename σ = (a.rename σ).substFree (σ x) (m.subst (fun v => .var (σ v))) := by
  induction a generalizing W with
  | plain p => simp only [substFree,rename,Agent.replaceVar_rename p x m σ hσ]
  | active y n => simp only [substFree,rename,Term.replaceVar_rename n x m σ hσ]
  | par a b ha hb => simp only [substFree,rename,ha x m σ hσ,hb x m σ hσ]
  | newVar a ih =>
    simp only [substFree,rename,ih (some x) (shiftTerm m) (Option.map σ) (Option.map_injective hσ),
      Option.map_some,shiftTerm_rename]

theorem substFree_mapNames (a : Extended V) (x : V) (m : Term V) (f g : Nat → Nat) :
    (a.substFree x m).mapNames f g = (a.mapNames f g).substFree x (m.mapNames f) := by
  induction a with
  | plain p => simp only [substFree,mapNames,Agent.mapNames_subst,replaceVar_mapNames]
  | active y n => simp only [substFree,mapNames,Term.mapNames_subst,replaceVar_mapNames]
  | par a b ha hb => simp only [substFree,mapNames,ha x m,hb x m]
  | newVar a ih => simp only [substFree,mapNames,ih (some x) (shiftTerm m),shiftTerm_mapNames]

theorem substFree_frameOf (a : Extended V) (x : V) (m : Term V) :
    (a.substFree x m).frameOf = a.frameOf.substFree x m := by
  induction a with
  | plain => rfl
  | active => rfl
  | par a b ha hb => simp only [substFree,frameOf,ha x m,hb x m]
  | newVar a ih => exact congrArg Extended.newVar (ih (some x) (shiftTerm m))

private theorem provider_middle (f a b : Extended V) : Structural (.par f (.par a b)) (.par a (.par f b)) :=
  (Structural.assoc f a b).symm.trans
    ((Structural.parLeft b (Structural.comm f a)).trans (Structural.assoc a f b))

/-- Figure 3 Subst through every current Extended context. The context must
not redefine the retained provider variable; active domains remain fixed. -/
theorem Structural.substExtended (x : V) (m : Term V) (a : Extended V) (ha : ¬ a.Exports x) :
    Structural (.par (.active x m) a) (.par (.active x m) (a.substFree x m)) := by
  induction a with
  | plain p => exact .substPlain x m p
  | active y n => exact .substActive x y m n ha
  | par a b ihA ihB =>
    have hA := ihA x m (fun h => ha (Or.inl h))
    have hB := ihB x m (fun h => ha (Or.inr h))
    exact (Structural.assoc _ _ _).symm.trans
      ((Structural.parLeft b hA).trans ((Structural.assoc _ _ _).trans
        ((provider_middle _ _ _).trans ((Structural.parRight _ hB).trans (provider_middle _ _ _).symm))))
  | newVar a ih =>
    exact (Structural.newPar (.active x m) a).trans
      ((Structural.newVar (ih (some x) (shiftTerm m) ha)).trans
        (Structural.newPar (.active x m) (a.substFree (some x) (shiftTerm m))).symm)

/-- Valid parallel active definitions automatically discharge the no-redefinition
premise required by the general source substitution derivation. -/
theorem Structural.substExtended_of_unique (x : V) (m : Term V) (a : Extended V)
    (hu : (Extended.par (.active x m) a).UniqueDefinitions) :
    Structural (.par (.active x m) a) (.par (.active x m) (a.substFree x m)) :=
  Structural.substExtended x m a (fun h => hu.2.2 x ⟨rfl,h⟩)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
