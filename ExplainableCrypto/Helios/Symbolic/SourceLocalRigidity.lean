import ExplainableCrypto.Helios.Symbolic.SourceFrameConstraints

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V W : Type}

/-- Every locally restricted value is uniquely determined modulo full E by
its surrounding environment whenever the complete local constraints hold.
Unsatisfiable components impose no uniqueness obligation. -/
def Rigid : {V : Type} → Extended V → (V → Ground) → Prop
  | _, .plain _, _ => True
  | _, .active _ _, _ => True
  | _, .par a b, env => a.Satisfies env → b.Satisfies env → a.Rigid env ∧ b.Rigid env
  | _, .newVar a, env =>
      (∀ m n, a.Satisfies (extendEnv env m) → a.Satisfies (extendEnv env n) → EqE m n) ∧
      ∀ m, a.Satisfies (extendEnv env m) → a.Rigid (extendEnv env m)

/-- Rigidity remains meaningful without an existence assumption: an
inconsistent constraint system has no competing local solutions. -/
theorem rigid_of_not_satisfies (a : Extended V) (env : V → Ground) (h : ¬ a.Satisfies env) :
    a.Rigid env := by
  cases a with
  | plain | active => trivial
  | par a b => exact fun ha hb => (h ⟨ha,hb⟩).elim
  | newVar a => exact ⟨fun m _ hm _ => (h ⟨m,hm⟩).elim,fun m hm => (h ⟨m,hm⟩).elim⟩

theorem rigid_rename (a : Extended V) (f : V → W) (env : W → Ground) :
    (a.rename f).Rigid env ↔ a.Rigid (fun v => env (f v)) := by
  induction a generalizing W with
  | plain | active => rfl
  | par a b ha hb => simp only [rename,Rigid,satisfies_rename,ha,hb]
  | newVar a ih =>
    simp only [rename,Rigid,satisfies_rename,ih]
    have he (m : Ground) : (fun v => extendEnv env m (Option.map f v)) =
        extendEnv (fun v => env (f v)) m := by funext v; cases v <;> rfl
    simp only [he]

theorem rigid_frameOf (a : Extended V) (env : V → Ground) :
    a.frameOf.Rigid env ↔ a.Rigid env := by
  induction a with
  | plain | active => rfl
  | par a b ha hb => simp only [frameOf,Rigid,satisfies_frameOf,ha,hb]
  | newVar a ih => simp only [frameOf,Rigid,satisfies_frameOf,ih]

private theorem rigid_par_iff (a b : Extended V) (env : V → Ground) :
    (Extended.par a b).Rigid env ↔ (b.Satisfies env → a.Rigid env) ∧ (a.Satisfies env → b.Rigid env) := by
  constructor
  · intro h
    constructor
    · intro hb
      by_cases ha : a.Satisfies env
      · exact (h ha hb).1
      · exact rigid_of_not_satisfies a env ha
    · intro ha
      by_cases hb : b.Satisfies env
      · exact (h ha hb).2
      · exact rigid_of_not_satisfies b env hb
  · rintro ⟨ha,hb⟩ ha' hb'
    exact ⟨ha hb',hb ha'⟩

/-- Source scope extrusion preserves all local solution choices and their
uniqueness. The old component does not acquire a dependency on the new binder. -/
theorem rigid_newPar (a : Extended V) (b : Extended (Option V)) (env : V → Ground) :
    (Extended.par a (.newVar b)).Rigid env ↔
      (Extended.newVar (.par (a.rename some) b)).Rigid env := by
  simp only [Rigid,Satisfies,satisfies_rename,rigid_rename]
  change (a.Satisfies env → (∃ m, b.Satisfies (extendEnv env m)) →
    a.Rigid env ∧ (∀ m n, b.Satisfies (extendEnv env m) → b.Satisfies (extendEnv env n) → EqE m n) ∧
      ∀ m, b.Satisfies (extendEnv env m) → b.Rigid (extendEnv env m)) ↔ _
  constructor
  · intro h
    constructor
    · intro m n hm hn
      exact (h hm.1 ⟨m,hm.2⟩).2.1 m n hm.2 hn.2
    · intro m hm ha hb
      exact ⟨(h ha ⟨m,hb⟩).1,(h ha ⟨m,hb⟩).2.2 m hb⟩
  · intro h ha ⟨m,hm⟩
    refine ⟨(h.2 m ⟨ha,hm⟩ ha hm).1,?_,?_⟩
    · intro v w hv hw
      exact h.1 v w ⟨ha,hv⟩ ⟨ha,hw⟩
    · intro v hv
      exact (h.2 v ⟨ha,hv⟩ ha hv).2

/-- All original variable/active structural rules preserve local-solution
rigidity; no normalization or satisfiability assumption is supplied. -/
theorem Structural.rigid {a b : Extended V} (h : Structural a b) (env : V → Ground) :
    a.Rigid env ↔ b.Rigid env := by
  induction h with
  | refl => rfl
  | symm _ ih => exact (ih env).symm
  | trans _ _ ih ih' => exact (ih env).trans (ih' env)
  | parLeft c h ih => simp only [Rigid,h.satisfies,ih]
  | parRight c h ih => simp only [Rigid,h.satisfies,ih]
  | newVar h ih => simp only [Rigid,h.satisfies,ih]
  | plainPar | substPlain | substActive => simp [Rigid]
  | rewrite => rfl
  | comm a b => simp only [Rigid]; aesop
  | zero a =>
    rw [rigid_par_iff]
    simp only [Satisfies,Rigid,true_implies,implies_true,and_true]
  | assoc a b c =>
    simp only [rigid_par_iff,Satisfies]
    aesop
  | newPar a b => exact rigid_newPar a b env
  | «alias» m =>
    simp only [Rigid,iff_true]
    refine ⟨?_,fun _ _ => True.intro⟩
    intro v w hv hw
    have hv' : EqE v (m.subst env) := by simpa only [Satisfies,shiftTerm_eval,extendEnv] using hv
    have hw' : EqE w (m.subst env) := by simpa only [Satisfies,shiftTerm_eval,extendEnv] using hw
    exact hv'.trans hw'.symm

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
