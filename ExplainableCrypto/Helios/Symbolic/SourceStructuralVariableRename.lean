import ExplainableCrypto.Helios.Symbolic.SourceVariableRenameTools

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V W : Type}

/-- Injective variable maps transport every active/variable structural rule.
Names and channels are unchanged; new Option binders stay distinct. -/
theorem Structural.rename {a b : Extended V} (h : Structural a b) (σ : V → W)
    (hσ : Function.Injective σ) : Structural (a.rename σ) (b.rename σ) := by
  induction h generalizing W with
  | refl => exact .refl _
  | symm h ih => exact (ih σ hσ).symm
  | trans h h' ih ih' => exact (ih σ hσ).trans (ih' σ hσ)
  | parLeft c h ih => exact .parLeft _ (ih σ hσ)
  | parRight a h ih => exact .parRight _ (ih σ hσ)
  | newVar h ih => exact .newVar (ih (Option.map σ) (option_map_injective σ hσ))
  | plainPar p q => exact .plainPar _ _
  | zero a => exact .zero _
  | assoc a b c => exact .assoc _ _ _
  | comm a b => exact .comm _ _
  | newPar a b =>
    simpa only [Extended.rename,Extended.rename_comp,Function.comp_def,Option.map_some] using
      Structural.newPar (a.rename σ) (b.rename (Option.map σ))
  | «alias» m =>
    simpa only [Extended.rename,Option.map_none,shiftTerm_rename,Agent.subst] using
      Structural.alias (m.subst (fun v => .var (σ v)))
  | substPlain x m p =>
    simpa only [Extended.rename,Agent.replaceVar_rename p x m σ hσ] using
      Structural.substPlain (σ x) (m.subst (fun v => .var (σ v))) (p.subst (fun v => .var (σ v)))
  | substActive x y m n hxy =>
    simpa only [Extended.rename,Term.replaceVar_rename n x m σ hσ] using
      Structural.substActive (σ x) (σ y) (m.subst (fun v => .var (σ v)))
        (n.subst (fun v => .var (σ v))) (fun h => hxy (hσ h))
  | rewrite x h => exact .rewrite (σ x) (h.subst _)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
