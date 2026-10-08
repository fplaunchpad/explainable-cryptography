import ExplainableCrypto.Helios.Symbolic.SourceRigidityBinders
import ExplainableCrypto.Helios.Symbolic.SourceSameRealizations

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
/-- A comparison relation packaging original Extended structural paths and
variable commutation already present in Named.Structural. This adds no action
or constructor to Extended.Structural; every comparison has a Named proof. -/
inductive BinderStructural : {V : Type} → Extended V → Extended V → Prop where
  | source {a b : Extended V} : Structural a b → BinderStructural a b
  | refl (a : Extended V) : BinderStructural a a
  | symm {a b : Extended V} : BinderStructural a b → BinderStructural b a
  | trans {a b c : Extended V} : BinderStructural a b → BinderStructural b c → BinderStructural a c
  | parLeft {a b : Extended V} (c : Extended V) : BinderStructural a b → BinderStructural (.par a c) (.par b c)
  | parRight (a : Extended V) {b c : Extended V} : BinderStructural b c → BinderStructural (.par a b) (.par a c)
  | newVar {a b : Extended (Option V)} : BinderStructural a b → BinderStructural (.newVar a) (.newVar b)
  | varComm (a : Extended (Option (Option V))) :
      BinderStructural (.newVar (.newVar a)) (.newVar (.newVar (a.rename swapBinders)))

variable {V : Type}

theorem Structural.binderStructural {a b : Extended V} (h : Structural a b) : BinderStructural a b := .source h

theorem BinderStructural.par {a a' b b' : Extended V}
    (h : BinderStructural a a') (j : BinderStructural b b') : BinderStructural (.par a b) (.par a' b') :=
  (h.parLeft b).trans (j.parRight a')

/-- All comparisons are actual source structural paths after embedding. -/
theorem BinderStructural.named {a b : Extended V} (h : BinderStructural a b) :
    Named.Structural (.embed a) (.embed b) := by
  induction h with
  | source h => exact .embed h
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih ij => exact ih.trans ij
  | parLeft c _ ih =>
    exact (Named.Structural.embedPar _ _).trans
      ((Named.Structural.parLeft _ ih).trans (Named.Structural.embedPar _ _).symm)
  | parRight c _ ih =>
    exact (Named.Structural.embedPar _ _).trans
      ((Named.Structural.parRight _ ih).trans (Named.Structural.embedPar _ _).symm)
  | newVar _ ih =>
    exact (Named.Structural.embedVar _).trans
      ((Named.Structural.newVar ih).trans (Named.Structural.embedVar _).symm)
  | varComm a =>
    rename_i U
    have unpack (b : Extended (Option (Option U))) :
        Named.Structural (.embed (.newVar (.newVar b))) (.newVar (.newVar (.embed b))) :=
      (Named.Structural.embedVar _).trans (Named.Structural.newVar (Named.Structural.embedVar _))
    exact (unpack a).trans ((Named.Structural.varComm (.embed a)).trans (unpack _).symm)

theorem BinderStructural.sameRealizations {a b : Extended V} (h : BinderStructural a b) : a.SameRealizations b := by
  induction h with
  | source h => exact h.sameRealizations
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih ij => exact ih.trans ij
  | parLeft c _ ih => exact ih.par (.refl c)
  | parRight c _ ih => exact (SameRealizations.refl c).par ih
  | newVar _ ih => exact ih.newVar
  | varComm a => exact sameRealizations_varComm a

theorem BinderStructural.satisfies {a b : Extended V} (h : BinderStructural a b) (env : V → Ground) :
    a.Satisfies env ↔ b.Satisfies env := by
  induction h with
  | source h => exact h.satisfies env
  | refl => rfl
  | symm _ ih => exact (ih env).symm
  | trans _ _ ih ij => exact (ih env).trans (ij env)
  | parLeft c _ ih => simp only [Satisfies,ih]
  | parRight c _ ih => simp only [Satisfies,ih]
  | newVar _ ih => simp only [Satisfies,ih]
  | varComm a =>
    simp only [Satisfies,satisfies_rename,extendEnv_swapBinders]
    exact exists_comm

theorem BinderStructural.rigid {a b : Extended V} (h : BinderStructural a b) (env : V → Ground) :
    a.Rigid env ↔ b.Rigid env := by
  induction h with
  | source h => exact h.rigid env
  | refl => rfl
  | symm _ ih => exact (ih env).symm
  | trans _ _ ih ij => exact (ih env).trans (ij env)
  | parLeft c h ih => simp only [Rigid,h.satisfies,ih]
  | parRight c h ih => simp only [Rigid,h.satisfies,ih]
  | newVar h ih => simp only [Rigid,h.satisfies,ih]
  | varComm a => exact rigid_varComm a env

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
