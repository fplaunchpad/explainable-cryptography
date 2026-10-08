import ExplainableCrypto.Helios.Symbolic.SourceFrameStructure
import ExplainableCrypto.Helios.Symbolic.SourceNameRestrictionRules

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V : Type}

theorem Extended.Reduction.frameOf {a b : Extended V} (h : Extended.Reduction a b) :
    Extended.Structural a.frameOf b.frameOf := by
  induction h with
  | atomComm => exact .refl _
  | thenBranch => exact .refl _
  | elseBranch => exact .refl _
  | parLeft c h ih => exact .parLeft _ ih
  | parRight a h ih => exact .parRight _ ih
  | newVar h ih => exact .newVar ih
  | congr ha h hb ih => exact ha.frameOf.trans (ih.trans hb.frameOf)

theorem Extended.FreeStep.frameOf {a b : Extended V} {l : Extended.FreeLabel V}
    (h : Extended.FreeStep a l b) : Extended.Structural a.frameOf b.frameOf := by
  induction h with
  | input => exact .refl _
  | output => exact .refl _
  | scopeInput h ih => exact .newVar ih
  | scopeOutput h ih => exact .newVar ih
  | parLeft c h ih => exact .parLeft _ ih
  | parRight a h ih => exact .parRight _ ih
  | congr ha h hb ih => exact ha.frameOf.trans (ih.trans hb.frameOf)

theorem Named.Reduction.frameOf {a b : Named V} (h : Named.Reduction a b) :
    Named.Structural a.frameOf b.frameOf := by
  induction h with
  | embed h => exact .embed h.frameOf
  | parLeft c h ih => exact .parLeft _ ih
  | parRight a h ih => exact .parRight _ ih
  | newName n h ih => exact .newName n ih
  | newVar h ih => exact .newVar ih
  | congr ha h hb ih => exact ha.frameOf.trans (ih.trans hb.frameOf)

theorem Named.FreeStep.frameOf {a b : Named V} {l : Extended.FreeLabel V}
    (h : Named.FreeStep a l b) : Named.Structural a.frameOf b.frameOf := by
  induction h with
  | embed h => exact .embed h.frameOf
  | scopeName n hf h ih => exact .newName n ih
  | scopeInput h ih => exact .newVar ih
  | scopeOutput h ih => exact .newVar ih
  | parLeft c h ih => exact .parLeft _ ih
  | parRight a h ih => exact .parRight _ ih
  | congr ha h hb ih => exact ha.frameOf.trans (ih.trans hb.frameOf)

/-- Reclosing an output in a left parallel component keeps its shifted old
context, then moves the variable restriction back to the emitting component. -/
theorem Named.Structural.reclose_parLeft (b : Named (Option V)) (d : Named V) :
    Named.Structural (.newVar (.par b (d.rename some))) (.par (.newVar b) d) := by
  exact (Named.Structural.newVar (Named.Structural.comm _ _)).trans
    ((Named.Structural.varPar d b).symm.trans (Named.Structural.comm _ _))

/-- Scope exchanged the local and exported binders; reclosing reverses that
exchange using the existing Named variable-commutation rule. -/
theorem Named.Structural.reclose_scope (b : Named (Option (Option V))) :
    Named.Structural (.newVar (.newVar (b.rename Extended.swapBinders)))
      (.newVar (.newVar b)) := (Named.Structural.varComm b).symm

/-- Bound output preserves the old frame after its freshly exported variable
is restricted again. Named Structural supplies the existing binder exchange. -/
theorem Extended.BoundOutput.frameOf_reclose {a : Extended V} {b : Extended (Option V)}
    {c : Nat} (h : Extended.BoundOutput a c b) :
    Named.Structural (.newVar (.embed b.frameOf)) (.embed a.frameOf) := by
  induction h with
  | openAtom h =>
    exact (Named.Structural.newVar (.embed h.frameOf.symm)).trans (Named.Structural.embedVar _).symm
  | scope h ih =>
    rename_i _ a b c
    simp only [Extended.frameOf,Extended.frameOf_rename]
    exact (Named.Structural.newVar (Named.Structural.embedVar _)).trans
      ((Named.Structural.reclose_scope (.embed b.frameOf)).trans
        ((Named.Structural.newVar ih).trans (Named.Structural.embedVar _).symm))
  | parLeft d h ih =>
    simp only [Extended.frameOf,Extended.frameOf_rename]
    exact (Named.Structural.newVar (Named.Structural.embedPar _ _)).trans
      ((Named.Structural.reclose_parLeft _ (.embed d.frameOf)).trans
        ((Named.Structural.parLeft _ ih).trans (Named.Structural.embedPar _ _).symm))
  | parRight a h ih =>
    simp only [Extended.frameOf,Extended.frameOf_rename]
    exact (Named.Structural.newVar (Named.Structural.embedPar _ _)).trans
      ((Named.Structural.varPar (.embed a.frameOf) _).symm.trans
        ((Named.Structural.parRight _ ih).trans (Named.Structural.embedPar _ _).symm))
  | congr ha h hb ih =>
    exact (Named.Structural.newVar (.embed hb.frameOf.symm)).trans
      (ih.trans (.embed ha.frameOf.symm))

/-- Every current Named bound-output constructor preserves the complete frame
under reclosure, including alpha/Struct paths and mixed name/variable Scope. -/
theorem Named.BoundOutput.frameOf_reclose {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : Named.BoundOutput a c b) : Named.Structural (.newVar b.frameOf) a.frameOf := by
  induction h with
  | embed h => exact h.frameOf_reclose
  | openAtom h => exact .newVar h.frameOf.symm
  | scopeName n hf h ih =>
    exact (Named.Structural.nameVarComm n _).symm.trans (.newName n ih)
  | scopeVar h ih =>
    simp only [Named.frameOf,Named.frameOf_rename]
    exact (Named.Structural.reclose_scope _).trans (.newVar ih)
  | parLeft d h ih =>
    simp only [Named.frameOf,Named.frameOf_rename]
    exact (Named.Structural.reclose_parLeft _ _).trans (.parLeft _ ih)
  | parRight a h ih =>
    simp only [Named.frameOf,Named.frameOf_rename]
    exact (Named.Structural.varPar _ _).symm.trans (.parRight _ ih)
  | congr ha h hb ih =>
    exact (Named.Structural.newVar hb.frameOf.symm).trans (ih.trans ha.frameOf.symm)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
