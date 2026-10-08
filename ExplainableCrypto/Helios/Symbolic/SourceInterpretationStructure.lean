import ExplainableCrypto.Helios.Symbolic.SourceActiveInterpretation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

theorem realizes_plainPar (a b : Agent V) (env : V → Ground) (p : Agent Empty) :
    (plain (.par a b)).Realizes env p ↔ (par (.plain a) (.plain b)).Realizes env p := by
  constructor
  · intro h
    exact ⟨a.subst env,b.subst env,.refl _,.refl _,h⟩
  · rintro ⟨q,r,hq,hr,h⟩
    exact (Agent.EvalEq.par hq hr).trans h

theorem realizes_zero (a : Extended V) (env : V → Ground) (p : Agent Empty) :
    (par a (.plain .nil)).Realizes env p ↔ a.Realizes env p := by
  constructor
  · rintro ⟨q,r,hq,hr,h⟩
    exact hq.congr ((Agent.EvalEq.of_parEq (Agent.ParEq.zero q).symm).trans
      ((Agent.EvalEq.par (.refl q) hr).trans h))
  · intro h
    exact ⟨p,.nil,h,.refl _,.of_parEq (.zero _)⟩

theorem realizes_comm (a b : Extended V) (env : V → Ground) (p : Agent Empty) :
    (par a b).Realizes env p ↔ (par b a).Realizes env p := by
  constructor <;> rintro ⟨q,r,hq,hr,h⟩ <;>
    exact ⟨r,q,hr,hq,(Agent.EvalEq.of_parEq (.comm _ _)).trans h⟩

theorem realizes_assoc (a b c : Extended V) (env : V → Ground) (p : Agent Empty) :
    (par (par a b) c).Realizes env p ↔ (par a (par b c)).Realizes env p := by
  constructor
  · rintro ⟨q,r,⟨s,t,hs,ht,hq⟩,hr,h⟩
    exact ⟨s,.par t r,hs,realizes_par _ _ _ ht hr,
      (Agent.EvalEq.of_parEq (Agent.ParEq.assoc _ _ _).symm).trans
        ((Agent.EvalEq.par hq (.refl r)).trans h)⟩
  · rintro ⟨q,r,hq,⟨s,t,hs,ht,hr⟩,h⟩
    exact ⟨.par q s,t,realizes_par _ _ _ hq hs,ht,
      (Agent.EvalEq.of_parEq (Agent.ParEq.assoc _ _ _)).trans
        ((Agent.EvalEq.par (.refl q) hr).trans h)⟩

theorem realizes_newPar (a : Extended V) (b : Extended (Option V)) (env : V → Ground)
    (p : Agent Empty) : (par a (.newVar b)).Realizes env p ↔
      (newVar (.par (a.rename some) b)).Realizes env p := by
  constructor
  · rintro ⟨q,r,hq,⟨m,hr⟩,h⟩
    refine ⟨m,q,r,?_,hr,h⟩
    exact (realizes_rename a some (extendEnv env m) q).mpr hq
  · rintro ⟨m,q,r,hq,hr,h⟩
    exact ⟨q,r,(realizes_rename a some (extendEnv env m) q).mp hq,⟨m,hr⟩,h⟩

theorem realizes_alias (m : Term V) (env : V → Ground) (p : Agent Empty) :
    (newVar (.active none (shiftTerm m))).Realizes env p ↔ (plain .nil).Realizes env p := by
  constructor
  · rintro ⟨v,_,h⟩
    exact h
  · intro h
    refine ⟨m.subst env,?_,h⟩
    simp only [shiftTerm,Term.subst_subst,Term.subst,extendEnv]
    exact .refl _

theorem subst_active_equivE (x : V) (m : Term V) (a : Agent V) (env : V → Ground)
    (hm : EqE (env x) (m.subst env)) :
    Agent.EquivE (a.subst env) ((a.subst (replaceVar x m)).subst env) := by
  classical
  rw [Agent.subst_subst]
  apply Agent.subst_equivE
  intro v
  by_cases hv : v=x
  · subst v
    simpa [replaceVar] using hm
  · simp only [replaceVar,if_neg hv,Term.subst]
    exact .refl _

theorem realizes_substPlain (x : V) (m : Term V) (a : Agent V) (env : V → Ground)
    (p : Agent Empty) : (par (.active x m) (.plain a)).Realizes env p ↔
      (par (.active x m) (.plain (a.subst (replaceVar x m)))).Realizes env p := by
  constructor
  · rintro ⟨q,r,hq,hr,h⟩
    exact ⟨q,r,hq,(Agent.EvalEq.of_equivE (subst_active_equivE x m a env hq.1).symm).trans hr,h⟩
  · rintro ⟨q,r,hq,hr,h⟩
    exact ⟨q,r,hq,(Agent.EvalEq.of_equivE (subst_active_equivE x m a env hq.1)).trans hr,h⟩

theorem subst_active_term_equivE (x : V) (m n : Term V) (env : V → Ground)
    (hm : EqE (env x) (m.subst env)) : EqE (n.subst env) ((n.subst (replaceVar x m)).subst env) := by
  classical
  rw [Term.subst_subst]
  apply Term.subst_congr
  intro v
  by_cases hv : v=x
  · subst v
    simpa [replaceVar] using hm
  · simp only [replaceVar,if_neg hv,Term.subst]
    exact .refl _

theorem realizes_substActive (x y : V) (m n : Term V) (env : V → Ground) (p : Agent Empty) :
    (par (.active x m) (.active y n)).Realizes env p ↔
      (par (.active x m) (.active y (n.subst (replaceVar x m)))).Realizes env p := by
  constructor
  · rintro ⟨q,r,hq,hr,h⟩
    exact ⟨q,r,hq,⟨hr.1.trans (subst_active_term_equivE x m n env hq.1),hr.2⟩,h⟩
  · rintro ⟨q,r,hq,hr,h⟩
    exact ⟨q,r,hq,⟨hr.1.trans (subst_active_term_equivE x m n env hq.1).symm,hr.2⟩,h⟩

theorem realizes_rewrite (x : V) {m n : Term V} (hm : EqE m n) (env : V → Ground)
    (p : Agent Empty) : (active x m).Realizes env p ↔ (active x n).Realizes env p :=
  ⟨fun h => ⟨h.1.trans (hm.subst env),h.2⟩,
   fun h => ⟨h.1.trans (hm.subst env).symm,h.2⟩⟩

/-- Every current active/variable structural rule preserves the interpretation,
including arbitrarily nested symmetric/transitive rewrites and contexts. -/
theorem Structural.realizes {a b : Extended V} (h : Structural a b)
    (env : V → Ground) (p : Agent Empty) : a.Realizes env p ↔ b.Realizes env p := by
  induction h generalizing p with
  | refl => exact Iff.rfl
  | symm h ih => exact (ih env p).symm
  | trans h h' ih ih' => exact (ih env p).trans (ih' env p)
  | parLeft c h ih => simp only [Realizes,ih]
  | parRight a h ih => simp only [Realizes,ih]
  | newVar h ih => simp only [Realizes,ih]
  | plainPar a b => exact realizes_plainPar a b env p
  | zero a => exact realizes_zero a env p
  | assoc a b c => exact realizes_assoc a b c env p
  | comm a b => exact realizes_comm a b env p
  | newPar a b => exact realizes_newPar a b env p
  | «alias» m => exact realizes_alias m env p
  | substPlain x m a => exact realizes_substPlain x m a env p
  | substActive x y m n hxy => exact realizes_substActive x y m n env p
  | rewrite x hm => exact realizes_rewrite x hm env p

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
