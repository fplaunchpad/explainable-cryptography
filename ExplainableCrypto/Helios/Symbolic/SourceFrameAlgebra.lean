import ExplainableCrypto.Helios.Symbolic.SourceVariableFramePrefix

namespace ExplainableCrypto.Helios.Symbolic

/-- Proof instrumentation for frame equations. Every model must respect the
existing full E and capture-avoiding substitution; no source rule is added. -/
structure FrameAlgebra where
  Value : Type
  eval : {V : Type} → (V → Value) → Term V → Value
  eval_var : ∀ {V : Type} (env : V → Value) (v : V), eval env (.var v) = env v
  eval_subst : ∀ {V W : Type} (env : W → Value) (t : Term V) (σ : V → Term W),
    eval env (t.subst σ) = eval (fun v => eval env (σ v)) t
  eval_eq : ∀ {V : Type} (env : V → Value) {s t : Term V}, EqE s t → eval env s = eval env t

namespace FrameAlgebra
open Historical.General.Source
variable (M : FrameAlgebra) {V W : Type}

def extend (env : V → M.Value) (m : M.Value) : Option V → M.Value
  | none => m
  | some v => env v

theorem eval_rename (env : W → M.Value) (t : Term V) (f : V → W) :
    M.eval env (t.subst (fun v => .var (f v))) = M.eval (fun v => env (f v)) t := by
  rw [M.eval_subst]
  simp only [M.eval_var]

theorem eval_shift (env : V → M.Value) (m : M.Value) (t : Term V) :
    M.eval (M.extend env m) (shiftTerm t) = M.eval env t := by
  rw [shiftTerm,M.eval_rename]
  rfl

theorem eval_replace (env : V → M.Value) (x : V) (m t : Term V)
    (h : env x = M.eval env m) : M.eval env (t.subst (replaceVar x m)) = M.eval env t := by
  classical
  rw [M.eval_subst]
  congr 1
  funext v
  by_cases hv : v = x
  · subst v; simp only [replaceVar]; exact h.symm
  · simp only [replaceVar,if_neg hv,M.eval_var]

def Satisfies (M : FrameAlgebra) : {V : Type} → Extended V → (V → M.Value) → Prop
  | _, .plain _, _ => True
  | _, .active x m, env => env x = M.eval env m
  | _, .par a b, env => M.Satisfies a env ∧ M.Satisfies b env
  | _, .newVar a, env => ∃ m, M.Satisfies a (M.extend env m)

def Rigid (M : FrameAlgebra) : {V : Type} → Extended V → (V → M.Value) → Prop
  | _, .plain _, _ => True
  | _, .active _ _, _ => True
  | _, .par a b, env => M.Satisfies a env → M.Satisfies b env → M.Rigid a env ∧ M.Rigid b env
  | _, .newVar a, env =>
      (∀ m n, M.Satisfies a (M.extend env m) → M.Satisfies a (M.extend env n) → m = n) ∧
      ∀ m, M.Satisfies a (M.extend env m) → M.Rigid a (M.extend env m)

theorem satisfies_rename (a : Extended V) (f : V → W) (env : W → M.Value) :
    M.Satisfies (a.rename f) env ↔ M.Satisfies a (fun v => env (f v)) := by
  induction a generalizing W with
  | plain => rfl
  | active x m => simp only [Extended.rename,Satisfies,M.eval_rename]
  | par a b ih ij => exact and_congr (ih f env) (ij f env)
  | newVar a ih =>
    simp only [Extended.rename,Satisfies,ih]
    have he (m : M.Value) : (fun v => M.extend env m (Option.map f v)) =
        M.extend (fun v => env (f v)) m := by funext v; cases v <;> rfl
    simp only [he]

theorem structural_satisfies {a b : Extended V} (h : Extended.Structural a b)
    (env : V → M.Value) : M.Satisfies a env ↔ M.Satisfies b env := by
  induction h with
  | refl => rfl
  | symm _ ih => exact (ih env).symm
  | trans _ _ ih ij => exact (ih env).trans (ij env)
  | parLeft c _ ih => exact and_congr (ih env) Iff.rfl
  | parRight c _ ih => exact and_congr Iff.rfl (ih env)
  | newVar _ ih => exact exists_congr (fun m => ih (M.extend env m))
  | plainPar => simp only [Satisfies,and_self]
  | zero => simp only [Satisfies,and_true]
  | assoc => simp only [Satisfies,and_assoc]
  | comm => exact and_comm
  | newPar a b =>
    simp only [Satisfies,M.satisfies_rename,extend]
    exact exists_and_left.symm
  | «alias» m => simp only [Satisfies,M.eval_shift,extend,exists_eq,iff_self]
  | substPlain => rfl
  | substActive x y m n hxy =>
    change (env x = M.eval env m ∧ env y = M.eval env n) ↔
      (env x = M.eval env m ∧ env y = M.eval env (n.subst (replaceVar x m)))
    exact and_congr_right (fun h => by rw [M.eval_replace env x m n h])
  | rewrite x h => simp only [Satisfies,M.eval_eq env h]

theorem rigid_of_not_satisfies (a : Extended V) (env : V → M.Value)
    (h : ¬ M.Satisfies a env) : M.Rigid a env := by
  cases a with
  | plain | active => trivial
  | par => exact fun ha hb => (h ⟨ha,hb⟩).elim
  | newVar => exact ⟨fun m _ hm _ => (h ⟨m,hm⟩).elim,fun m hm => (h ⟨m,hm⟩).elim⟩

theorem rigid_rename (a : Extended V) (f : V → W) (env : W → M.Value) :
    M.Rigid (a.rename f) env ↔ M.Rigid a (fun v => env (f v)) := by
  induction a generalizing W with
  | plain | active => rfl
  | par a b ih ij => simp only [Extended.rename,Rigid,M.satisfies_rename,ih,ij]
  | newVar a ih =>
    simp only [Extended.rename,Rigid,M.satisfies_rename,ih]
    have he (m : M.Value) : (fun v => M.extend env m (Option.map f v)) =
        M.extend (fun v => env (f v)) m := by funext v; cases v <;> rfl
    simp only [he]

private theorem rigid_par_iff (a b : Extended V) (env : V → M.Value) :
    M.Rigid (.par a b) env ↔
      (M.Satisfies b env → M.Rigid a env) ∧ (M.Satisfies a env → M.Rigid b env) := by
  constructor
  · intro h
    constructor
    · intro hb
      by_cases ha : M.Satisfies a env
      · exact (h ha hb).1
      · exact M.rigid_of_not_satisfies a env ha
    · intro ha
      by_cases hb : M.Satisfies b env
      · exact (h ha hb).2
      · exact M.rigid_of_not_satisfies b env hb
  · rintro ⟨ha,hb⟩ ha' hb'
    exact ⟨ha hb',hb ha'⟩

theorem rigid_newPar (a : Extended V) (b : Extended (Option V)) (env : V → M.Value) :
    M.Rigid (.par a (.newVar b)) env ↔ M.Rigid (.newVar (.par (a.rename some) b)) env := by
  simp only [Rigid,Satisfies,M.satisfies_rename,M.rigid_rename]
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

theorem structural_rigid {a b : Extended V} (h : Extended.Structural a b)
    (env : V → M.Value) : M.Rigid a env ↔ M.Rigid b env := by
  induction h with
  | refl => rfl
  | symm _ ih => exact (ih env).symm
  | trans _ _ ih ij => exact (ih env).trans (ij env)
  | parLeft c h ih => simp only [Rigid,M.structural_satisfies h,ih]
  | parRight c h ih => simp only [Rigid,M.structural_satisfies h,ih]
  | newVar h ih => simp only [Rigid,M.structural_satisfies h,ih]
  | plainPar | substPlain | substActive => simp [Rigid]
  | rewrite => rfl
  | comm a b => simp only [Rigid]; aesop
  | zero a => rw [M.rigid_par_iff]; simp only [Satisfies,Rigid,true_implies,implies_true,and_true]
  | assoc a b c => simp only [M.rigid_par_iff,Satisfies]; aesop
  | newPar a b => exact M.rigid_newPar a b env
  | «alias» m =>
    simp only [Rigid,iff_true]
    refine ⟨?_,fun _ _ => True.intro⟩
    intro v w hv hw
    change v = M.eval (M.extend env v) (shiftTerm m) at hv
    change w = M.eval (M.extend env w) (shiftTerm m) at hw
    rw [M.eval_shift] at hv hw
    exact hv.trans hw.symm

def groundValue (m : Ground) : M.Value := M.eval Empty.elim m

theorem eval_ground_env (env : V → Ground) (t : Term V) :
    M.eval (fun v => M.groundValue (env v)) t = M.groundValue (t.subst env) :=
  (M.eval_subst Empty.elim t env).symm

theorem eval_groundTerm (env : V → M.Value) (t : Ground) :
    M.eval env (Extended.groundTerm t) = M.groundValue t := by
  rw [Extended.groundTerm,M.eval_subst]
  congr 1
  funext v
  exact v.elim

theorem extend_ground (env : V → Ground) (m : Ground) :
    (fun v => M.groundValue (extendEnv env m v)) =
      M.extend (fun v => M.groundValue (env v)) (M.groundValue m) := by
  funext v
  cases v <;> rfl

/-- Original ground solutions map into every algebra; all cryptographic
reasoning is carried by the existing EqE derivations in the solution. -/
theorem satisfies_of_ground {a : Extended V} {env : V → Ground} (h : a.Satisfies env) :
    M.Satisfies a (fun v => M.groundValue (env v)) := by
  induction a with
  | plain => trivial
  | active x m =>
    change M.groundValue (env x) = M.eval (fun v => M.groundValue (env v)) m
    rw [M.eval_ground_env]
    exact M.eval_eq Empty.elim h
  | par a b ih ij => exact ⟨ih h.1,ij h.2⟩
  | newVar a ih =>
    obtain ⟨m,hm⟩ := h
    exact ⟨M.groundValue m,by simpa only [M.extend_ground] using ih hm⟩

theorem frameEntries_satisfies_iff (n : Nat) (vars : Fin n → V) (values : Fin n → Ground)
    (env : V → M.Value) : M.Satisfies (Extended.frameEntries n vars values) env ↔
      ∀ i, env (vars i) = M.groundValue (values i) := by
  induction n with
  | zero => exact ⟨fun _ i => Fin.elim0 i,fun _ => True.intro⟩
  | succ n ih =>
    simp only [Extended.frameEntries,Satisfies,M.eval_groundTerm,ih]
    constructor
    · rintro ⟨ha,hb⟩ i
      exact Fin.lastCases ha hb i
    · intro h
      exact ⟨h (Fin.last n),fun i => h i.castSucc⟩

theorem activeFrame_satisfies_iff {r : Finset Nat} {handles : Nat} (φ : Frame r handles)
    (env : Fin handles → M.Value) : M.Satisfies (Extended.activeFrame φ) env ↔
      ∀ i, env i = M.groundValue (φ.value i) :=
  M.frameEntries_satisfies_iff handles id φ.value env

theorem satisfies_frameOf (a : Extended V) (env : V → M.Value) :
    M.Satisfies a.frameOf env ↔ M.Satisfies a env := by
  induction a <;> simp_all only [Extended.frameOf,Satisfies]

theorem rigid_frameOf (a : Extended V) (env : V → M.Value) :
    M.Rigid a.frameOf env ↔ M.Rigid a env := by
  induction a <;> simp_all only [Extended.frameOf,Rigid,M.satisfies_frameOf]

theorem extend_swap (env : V → M.Value) (m n : M.Value) :
    (fun v => M.extend (M.extend env m) n (Extended.swapBinders v)) =
      M.extend (M.extend env n) m := by
  funext v
  cases v with
  | none => rfl
  | some v => cases v <;> rfl

private theorem rigid_swapped (a : Extended (Option (Option V))) (env : V → M.Value)
    (h : M.Rigid (.newVar (.newVar a)) env) :
    M.Rigid (.newVar (.newVar (a.rename Extended.swapBinders))) env := by
  simp only [Rigid,Satisfies,M.satisfies_rename,M.rigid_rename,M.extend_swap] at h ⊢
  constructor
  · intro m n ⟨v,hv⟩ ⟨w,hw⟩
    have hvw := h.1 v w ⟨m,hv⟩ ⟨n,hw⟩
    subst w
    exact (h.2 v ⟨m,hv⟩).1 m n hv hw
  · intro m ⟨v,hv⟩
    constructor
    · intro v w hv hw
      exact h.1 v w ⟨m,hv⟩ ⟨m,hw⟩
    · intro w hw
      exact (h.2 w ⟨m,hw⟩).2 m hw

theorem rigid_varComm (a : Extended (Option (Option V))) (env : V → M.Value) :
    M.Rigid (.newVar (.newVar a)) env ↔
      M.Rigid (.newVar (.newVar (a.rename Extended.swapBinders))) env := by
  constructor
  · exact M.rigid_swapped a env
  · intro h
    have hh := M.rigid_swapped (a.rename Extended.swapBinders) env h
    have he : (Extended.swapBinders ∘ Extended.swapBinders : Option (Option V) → _) = id :=
      funext Extended.swapBinders_involutive
    simpa only [Extended.rename_comp,he,Extended.rename_id] using hh

theorem binder_satisfies {a b : Extended V} (h : a.BinderStructural b)
    (env : V → M.Value) : M.Satisfies a env ↔ M.Satisfies b env := by
  induction h with
  | source h => exact M.structural_satisfies h env
  | refl => rfl
  | symm _ ih => exact (ih env).symm
  | trans _ _ ih ij => exact (ih env).trans (ij env)
  | parLeft c _ ih => exact and_congr (ih env) Iff.rfl
  | parRight c _ ih => exact and_congr Iff.rfl (ih env)
  | newVar _ ih => exact exists_congr (fun m => ih (M.extend env m))
  | varComm a =>
    simp only [Satisfies,M.satisfies_rename,M.extend_swap]
    exact exists_comm

theorem binder_rigid {a b : Extended V} (h : a.BinderStructural b)
    (env : V → M.Value) : M.Rigid a env ↔ M.Rigid b env := by
  induction h with
  | source h => exact M.structural_rigid h env
  | refl => rfl
  | symm _ ih => exact (ih env).symm
  | trans _ _ ih ij => exact (ih env).trans (ij env)
  | parLeft c h ih => simp only [Rigid,M.binder_satisfies h,ih]
  | parRight c h ih => simp only [Rigid,M.binder_satisfies h,ih]
  | newVar h ih => simp only [Rigid,M.binder_satisfies h,ih]
  | varComm a => exact M.rigid_varComm a env

theorem frameEntries_rigid (n : Nat) (vars : Fin n → V) (values : Fin n → Ground)
    (env : V → M.Value) : M.Rigid (Extended.frameEntries n vars values) env := by
  induction n with
  | zero => trivial
  | succ n ih => exact fun _ _ => ⟨True.intro,ih _ _⟩

theorem activeFrame_rigid {r : Finset Nat} {handles : Nat} (φ : Frame r handles)
    (env : Fin handles → M.Value) : M.Rigid (Extended.activeFrame φ) env :=
  M.frameEntries_rigid handles id φ.value env

end FrameAlgebra
namespace Historical.General.Source.Named
variable {handles : Nat} {r hidden : Finset Nat}

/-- Actual presentation, rather than ground-only semantic comparison, derives
hidden-value uniqueness in every full-E algebra and every chosen name opening. -/
theorem RepresentsFrame.opening_algebra_rigid {a : Named (Fin handles)} {φ : Frame r handles}
    (h : a.RepresentsFrame hidden φ) {ρ : NameAssignment} {ns : List SourceName}
    {b : Extended (Fin handles)} (ho : Opens a ρ ns b) (M : FrameAlgebra)
    (env : Fin handles → M.Value) : M.Rigid b env := by
  obtain ⟨f,hf⟩ := h.opening_presentation ho
  exact (M.rigid_frameOf b env).mp ((M.binder_rigid hf env).mpr (M.activeFrame_rigid _ env))

/-- The actual old presentation and output reclosure determine the newly
public value in every equation algebra, not just among concrete ground terms. -/
theorem BoundOutput.opened_value_unique {a : Named (Fin handles)}
    {b : Named (Option (Fin handles))} {c : Nat} {φ : Frame r handles}
    (h : BoundOutput a c b) (hp : a.RepresentsFrame hidden φ)
    {ρ : NameAssignment} {ns : List SourceName} {d : Extended (Option (Fin handles))}
    (ho : Opens b ρ ns d) (M : FrameAlgebra) (env : Fin handles → M.Value)
    (m n : M.Value) (hm : M.Satisfies d (M.extend env m))
    (hn : M.Satisfies d (M.extend env n)) : m = n :=
  ((hp.bound_reclose h).opening_algebra_rigid (.newVar ho) M env).1 m n hm hn

/-- Actual reclosure derives a ground value and the old frame coordinates.
Every algebraic solution has exactly these values. The capture congruence
instantiation needed for a target Structural presentation is still separate. -/
theorem BoundOutput.opened_algebra_values {a : Named (Fin handles)}
    {b : Named (Option (Fin handles))} {c : Nat} {φ : Frame r handles}
    (h : BoundOutput a c b) (hp : a.RepresentsFrame hidden φ)
    {ρ : NameAssignment} {ns : List SourceName} {d : Extended (Option (Fin handles))}
    (ho : Opens b ρ ns d) :
    ∃ (f : Nat → Nat) (m : Ground),
      d.Satisfies (extendEnv (φ.mapNames f).value m) ∧
      ∀ (M : FrameAlgebra) (env : Fin handles → M.Value) (v : M.Value),
        M.Satisfies d (M.extend env v) →
          (∀ i, env i = M.groundValue ((φ.mapNames f).value i)) ∧ v = M.groundValue m := by
  obtain ⟨f,hs⟩ := (hp.bound_reclose h).opening_presentation (.newVar ho)
  have hg : (Extended.newVar d).Satisfies (φ.mapNames f).value :=
    (Extended.satisfies_frameOf _ _).mp ((hs.satisfies _).mpr
      ((Extended.activeFrame_satisfies_iff _ _).mpr (fun _ => .refl _)))
  obtain ⟨m,hm⟩ := hg
  refine ⟨f,m,hm,?_⟩
  intro M env v hv
  have hcan := (M.binder_satisfies hs env).mp
    ((M.satisfies_frameOf (.newVar d) env).mpr ⟨v,hv⟩)
  have hold := (M.activeFrame_satisfies_iff _ env).mp hcan
  refine ⟨hold,?_⟩
  have he : env = fun i => M.groundValue ((φ.mapNames f).value i) := funext hold
  subst env
  apply h.opened_value_unique hp ho M _ v (M.groundValue m) hv
  simpa only [M.extend_ground] using M.satisfies_of_ground hm

end Historical.General.Source.Named
end ExplainableCrypto.Helios.Symbolic
