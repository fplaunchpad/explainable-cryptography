import ExplainableCrypto.Helios.Symbolic.SourceExtendedInstantiation
import ExplainableCrypto.Helios.Symbolic.SourceInterpretationStructure

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V W : Type}

/-- A substitution graph also preserves the entire interpretation, including
all active constraints and the chosen plain body. -/
theorem Instantiates.realizes {σ : V → Term W} {a : Extended V} {b : Extended W}
    (h : Instantiates σ a b) (env : W → Ground) (p : Agent Empty) :
    b.Realizes env p ↔ a.Realizes (fun v => (σ v).subst env) p := by
  induction h generalizing p with
  | plain σ q => simp only [Realizes,Agent.subst_subst]
  | active σ x y m hy => simp only [Realizes,Term.subst_subst,hy,Term.subst]
  | par _ _ ha hb => simp only [Realizes,ha,hb]
  | newVar h ih =>
    simp only [Realizes,ih]
    apply exists_congr
    intro m
    apply Iff.of_eq
    congr 1
    funext v
    cases v with
    | none => rfl
    | some v => simp only [liftSubst,Term.subst_subst,Term.subst,extendEnv]

/-- Substitute the provider throughout an arbitrary extended context, extrude
the now-unused variable and discharge Alias. No new structural rule is added. -/
theorem Structural.let_normalize (m : Term V) {a : Extended (Option V)} {b : Extended V}
    (ha : ¬ a.Exports none) (h : Instantiates (inputSubst m) a b) :
    Structural (.newVar (.par (.active none (shiftTerm m)) a)) b := by
  have hs := Structural.newVar (Structural.substExtended none (shiftTerm m) a ha)
  rw [h.replace_fresh m ha] at hs
  exact hs.trans ((Structural.newVar (Structural.comm _ _)).trans
    ((Structural.newPar b (.active none (shiftTerm m))).symm.trans
      ((Structural.parRight b (Structural.alias m)).trans (Structural.zero b))))

/-- Every context that does not redefine the fresh local has an exact
instantiation and an actual source normalization path, even when V is empty. -/
theorem let_normalize_exists (m : Term V) (a : Extended (Option V))
    (ha : ¬ a.Exports none) :
    ∃ b, Instantiates (inputSubst m) a b ∧
      Structural (.newVar (.par (.active none (shiftTerm m)) a)) b := by
  obtain ⟨b,hb⟩ := instantiates_exists a (inputSubst m) (by
    intro x hx
    cases x with
    | none => exact (ha hx).elim
    | some x => exact ⟨x,rfl⟩)
  exact ⟨b,hb,Structural.let_normalize m ha hb⟩

theorem let_normalize_of_unique (m : Term V) (a : Extended (Option V))
    (hu : (Extended.newVar (.par (.active none (shiftTerm m)) a)).UniqueDefinitions) :
    ∃ b, Instantiates (inputSubst m) a b ∧
      Structural (.newVar (.par (.active none (shiftTerm m)) a)) b :=
  let_normalize_exists m a (fun h => hu.1.2.2 none ⟨rfl,h⟩)

/-- All surviving exported domains are exactly the old ones; local elimination
does not introduce or erase any public handle. -/
theorem Instantiates.local_exports (m : Term V) {a : Extended (Option V)} {b : Extended V}
    (ha : ¬ a.Exports none) (h : Instantiates (inputSubst m) a b) (v : V) :
    b.Exports v ↔ a.Exports (some v) := by
  have he := (Structural.let_normalize m ha h).exports v
  simpa only [Exports,Option.some_ne_none,false_or] using he.symm

/-- The original local constraint is interpreted by exactly the instantiated
context; all remaining values and the body stay explicit. -/
theorem Instantiates.local_realizes (m : Term V) {a : Extended (Option V)} {b : Extended V}
    (h : Instantiates (inputSubst m) a b) (env : V → Ground) (p : Agent Empty) :
    b.Realizes env p ↔ a.Realizes (extendEnv env (m.subst env)) p := by
  have he := h.realizes env p
  have hs : (fun v => (inputSubst m v).subst env) = extendEnv env (m.subst env) := by
    funext v
    cases v <;> rfl
  rwa [hs] at he

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
