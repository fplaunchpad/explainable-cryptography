import ExplainableCrypto.Helios.Symbolic.SourceFreshOperationalPrenex

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V W U : Type}

theorem option_map_injective (σ : V → W) (hσ : Function.Injective σ) :
    Function.Injective (Option.map σ) := by
  intro a b h
  cases a with
  | none => cases b <;> cases h; rfl
  | some a =>
    cases b with
    | none => cases h
    | some b => exact congrArg some (hσ (Option.some.inj h))

theorem liftSubst_rename (σ : V → W) :
    liftSubst (fun v => Term.var (σ v)) = fun v => Term.var (Option.map σ v) := by
  funext v
  cases v <;> rfl

theorem shiftTerm_rename (m : Term V) (σ : V → W) :
    (shiftTerm m).subst (fun v => .var (Option.map σ v)) =
      shiftTerm (m.subst (fun v => .var (σ v))) := by
  simp only [shiftTerm,Term.subst_subst,Term.subst,Option.map_some]

/-- Injectivity prevents a distinct old variable from acquiring the substituted
variable's image. Payloads and all uses then rename coherently. -/
theorem replaceVar_rename (x : V) (m : Term V) (σ : V → W) (hσ : Function.Injective σ) (v : V) :
    (replaceVar x m v).subst (fun v => .var (σ v)) =
      replaceVar (σ x) (m.subst (fun v => .var (σ v))) (σ v) := by
  classical
  by_cases hv : v=x
  · subst v; simp [replaceVar]
  · have hs : σ v ≠ σ x := fun h => hv (hσ h)
    simp only [replaceVar,if_neg hv,if_neg hs,Term.subst]

theorem Term.replaceVar_rename (t : Term V) (x : V) (m : Term V) (σ : V → W)
    (hσ : Function.Injective σ) :
    (t.subst (replaceVar x m)).subst (fun v => .var (σ v)) =
      (t.subst (fun v => .var (σ v))).subst (replaceVar (σ x) (m.subst (fun v => .var (σ v)))) := by
  simp only [Term.subst_subst,Term.subst,Source.replaceVar_rename x m σ hσ]

theorem Agent.replaceVar_rename (p : Agent V) (x : V) (m : Term V) (σ : V → W)
    (hσ : Function.Injective σ) :
    (p.subst (replaceVar x m)).subst (fun v => .var (σ v)) =
      (p.subst (fun v => .var (σ v))).subst (replaceVar (σ x) (m.subst (fun v => .var (σ v)))) := by
  simp only [Agent.subst_subst,Term.subst]
  congr 1
  funext v
  exact Source.replaceVar_rename x m σ hσ v

theorem Formula.nameSupport_rename (p : Formula V) (σ : V → W) :
    (p.subst (fun v => .var (σ v))).nameSupport = p.nameSupport := by
  induction p <;> simp_all only [Formula.subst,Formula.nameSupport,Term.nameSupport_rename]

theorem Agent.nameSupport_rename (p : Agent V) (σ : V → W) :
    (p.subst (fun v => .var (σ v))).nameSupport = p.nameSupport := by
  induction p generalizing W with
  | nil => rfl
  | par p q hp hq => simp only [Agent.subst,Agent.nameSupport,hp,hq]
  | output c m p hp => simp only [Agent.subst,Agent.nameSupport,Term.nameSupport_rename,hp]
  | input c p hp => simp only [Agent.subst,Agent.nameSupport,liftSubst_rename,hp]
  | branch f p q hp hq => simp only [Agent.subst,Agent.nameSupport,Formula.nameSupport_rename,hp,hq]

theorem Extended.nameSupport_rename (a : Extended V) (σ : V → W) :
    (a.rename σ).nameSupport = a.nameSupport := by
  induction a generalizing W with
  | plain p => exact p.nameSupport_rename σ
  | active x m => simp only [Extended.rename,Extended.nameSupport,Term.nameSupport_rename]
  | par a b ha hb => simp only [Extended.rename,Extended.nameSupport,ha,hb]
  | newVar a ih => exact ih (Option.map σ)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
