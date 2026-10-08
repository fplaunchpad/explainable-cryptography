import ExplainableCrypto.Helios.Symbolic.SourceFrameAlgebraQuotient
import ExplainableCrypto.Helios.Symbolic.SourceLocalCaptureNormalization

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V W : Type}

/-- The original frame with one genuinely fresh active observation. -/
def captureFrame (f : Extended V) (r : Term V) : Extended (Option V) :=
  .par (f.rename some) (.active none (shiftTerm r))

/-- This equality is an actual source structural path, not semantic equality
or an extra structural constructor. Both endpoints retain the complete frame. -/
def CapturedEq (f : Extended V) (r s : Term V) : Prop :=
  Structural (captureFrame f r) (captureFrame f s)

theorem CapturedEq.refl (f : Extended V) (r : Term V) : CapturedEq f r r := Structural.refl _
theorem CapturedEq.symm {f : Extended V} {r s : Term V} (h : CapturedEq f r s) :
    CapturedEq f s r := Structural.symm h
theorem CapturedEq.trans {f : Extended V} {r s t : Term V}
    (h : CapturedEq f r s) (j : CapturedEq f s t) : CapturedEq f r t := Structural.trans h j

theorem CapturedEq.of_eqE (f : Extended V) {r s : Term V} (h : EqE r s) : CapturedEq f r s :=
  Structural.parRight _ (.rewrite _ (h.subst (fun v => .var (some v))))

/-- Actual frame rearrangement transports the entire capture equality. -/
theorem CapturedEq.frame_structural {f g : Extended V} (h : Structural f g)
    {r s : Term V} (he : CapturedEq f r s) : CapturedEq g r s :=
  (Structural.parLeft _ (h.rename some (Option.some_injective _))).symm.trans
    (Structural.trans he (Structural.parLeft _ (h.rename some (Option.some_injective _))))

/-- A fresh local holding u can feed one selected hole in a term context. The
rest of that context keeps every old variable, including other occurrences. -/
private theorem capture_context_normalize (f : Extended V) (u : Term V) (C : Term (Option V)) :
    Structural
      (.newVar (.par
        ((captureFrame f u).rename (Option.map some))
        (.active (some none) (C.subst (fun v => match v with
          | none => .var none
          | some v => .var (some (some v)))))))
      (captureFrame f (bindInput C u)) := by
  let obs : Extended (Option (Option V)) := .active (some none)
    (C.subst (fun v => match v with
      | none => .var none
      | some v => .var (some (some v))))
  have he : (C.subst (fun v => match v with
      | none => .var none
      | some v => .var (some (some v)))).subst (inputSubst (shiftTerm u)) =
      shiftTerm (bindInput C u) := by
    simp only [Term.subst_subst,shiftTerm,bindInput]
    congr 1
    funext v
    cases v <;> rfl
  have hi : Instantiates (inputSubst (shiftTerm u)) obs
      (.active none (shiftTerm (bindInput C u))) := by
    simpa only [he] using Instantiates.active (inputSubst (shiftTerm u)) (some none) none
      (C.subst (fun v => match v with
        | none => .var none
        | some v => .var (some (some v)))) rfl
  have hn := Structural.let_normalize (shiftTerm u) (by simp [obs,Exports]) hi
  have hf : (f.rename some).rename (Option.map some) = (f.rename some).rename some := by
    simp only [rename_comp]
    congr 1
  have hu : (shiftTerm u).subst (fun v => .var (Option.map some v)) = shiftTerm (shiftTerm u) := by
    simp only [shiftTerm,Term.subst_subst]
    congr 1
  change Structural (.newVar (.par (.par ((f.rename some).rename (Option.map some))
    (.active none ((shiftTerm u).subst (fun v => .var (Option.map some v))))) obs)) _
  rw [hf,hu]
  exact (Structural.newVar (Structural.assoc _ _ _)).trans
    ((Structural.newPar (f.rename some) _).symm.trans (Structural.parRight _ hn))

/-- Contextual congruence is derived using the fresh local, rather than treating
simultaneous active substitution as a rule for one arbitrary occurrence. -/
theorem CapturedEq.context {f : Extended V} {r s : Term V} (h : CapturedEq f r s)
    (C : Term (Option V)) : CapturedEq f (bindInput C r) (bindInput C s) := by
  have hs := Structural.newVar (Structural.parLeft
    (.active (some none) (C.subst (fun v => match v with
      | none => .var none
      | some v => .var (some (some v)))))
    (h.rename (Option.map some) (Option.map_injective (Option.some_injective _))))
  exact (capture_context_normalize f r C).symm.trans
    (hs.trans (capture_context_normalize f s C))

private theorem captureFrame_par (a b : Extended V) (r : Term V) :
    Structural (captureFrame (.par a b) r) (.par (captureFrame a r) (b.rename some)) :=
  (Structural.assoc _ _ _).trans
    ((Structural.parRight _ (Structural.comm _ _)).trans (Structural.assoc _ _ _).symm)

theorem CapturedEq.parLeft {f : Extended V} {r s : Term V} (h : CapturedEq f r s)
    (g : Extended V) : CapturedEq (.par f g) r s :=
  (captureFrame_par f g r).trans
    ((Structural.parLeft _ h).trans (captureFrame_par f g s).symm)

theorem CapturedEq.parRight {f : Extended V} {r s : Term V} (h : CapturedEq f r s)
    (g : Extended V) : CapturedEq (.par g f) r s :=
  (h.parLeft g).frame_structural (Structural.comm _ _)

/-- The observed variable and its provider are distinct active domains. The
provider remains present while the fresh observation takes its full value. -/
theorem CapturedEq.provider (x : V) (m : Term V) : CapturedEq (.active x m) (.var x) m := by
  change Structural (.par (.active (some x) (shiftTerm m)) (.active none (.var (some x))))
    (.par (.active (some x) (shiftTerm m)) (.active none (shiftTerm m)))
  simpa only [Term.subst,replaceVar,ite_true] using
    Structural.substActive (some x) none (shiftTerm m) (.var (some x)) (Option.some_ne_none x)

theorem CapturedEq.unary {f : Extended V} {r s : Term V} (h : CapturedEq f r s)
    (op : Unary) : CapturedEq f (.unary op r) (.unary op s) := by
  simpa only [bindInput,Term.subst,inputSubst] using h.context (.unary op (.var none))

theorem CapturedEq.binary {f : Extended V} {a a' b b' : Term V}
    (ha : CapturedEq f a a') (hb : CapturedEq f b b') (op : Binary) :
    CapturedEq f (.binary op a b) (.binary op a' b') := by
  have h₁ := ha.context (.binary op (.var none) (shiftTerm b))
  have h₂ := hb.context (.binary op (shiftTerm a') (.var none))
  simp only [bindInput,Term.subst,shiftTerm,Term.subst_subst,inputSubst,Term.subst_var] at h₁ h₂
  exact h₁.trans h₂

theorem CapturedEq.ternary {f : Extended V} {a a' b b' c c' : Term V}
    (ha : CapturedEq f a a') (hb : CapturedEq f b b') (hc : CapturedEq f c c') (op : Ternary) :
    CapturedEq f (.ternary op a b c) (.ternary op a' b' c') := by
  have h₁ := ha.context (.ternary op (.var none) (shiftTerm b) (shiftTerm c))
  have h₂ := hb.context (.ternary op (shiftTerm a') (.var none) (shiftTerm c))
  have h₃ := hc.context (.ternary op (shiftTerm a') (shiftTerm b') (.var none))
  simp only [bindInput,Term.subst,shiftTerm,Term.subst_subst,inputSubst,Term.subst_var] at h₁ h₂ h₃
  exact h₁.trans (h₂.trans h₃)

theorem CapturedEq.spk {f : Extended V} {a a' b b' c c' d d' : Term V}
    (ha : CapturedEq f a a') (hb : CapturedEq f b b')
    (hc : CapturedEq f c c') (hd : CapturedEq f d d') :
    CapturedEq f (.spk a b c d) (.spk a' b' c' d') := by
  have h₁ := ha.context (.spk (.var none) (shiftTerm b) (shiftTerm c) (shiftTerm d))
  have h₂ := hb.context (.spk (shiftTerm a') (.var none) (shiftTerm c) (shiftTerm d))
  have h₃ := hc.context (.spk (shiftTerm a') (shiftTerm b') (.var none) (shiftTerm d))
  have h₄ := hd.context (.spk (shiftTerm a') (shiftTerm b') (shiftTerm c') (.var none))
  simp only [bindInput,Term.subst,shiftTerm,Term.subst_subst,inputSubst,Term.subst_var] at h₁ h₂ h₃ h₄
  exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- Full term congruence, including every SPK field, for the concrete
structural capture relation required by the quotient construction. -/
theorem CapturedEq.subst_congr (f : Extended W) (t : Term V) (σ τ : V → Term W)
    (h : ∀ v, CapturedEq f (σ v) (τ v)) : CapturedEq f (t.subst σ) (t.subst τ) := by
  induction t with
  | name | const => exact .refl _ _
  | var v => exact h v
  | unary op t ih => exact ih.unary op
  | binary op a b ih ij => exact ih.binary ij op
  | ternary op a b c ih ij ik => exact ih.ternary ij ik op
  | spk a b c d ih ij ik il => exact ih.spk ij ik il

private theorem captureFrame_scope (a : Extended (Option V)) (r : Term V) :
    Structural (captureFrame (.newVar a) r)
      (.newVar ((captureFrame a (shiftTerm r)).rename swapBinders)) := by
  have ha : (a.rename some).rename swapBinders = a.rename (Option.map some) := by
    rw [rename_comp]
    congr 1
    funext v
    cases v <;> rfl
  have hr : (shiftTerm (shiftTerm r)).subst (fun v => .var (swapBinders v)) =
      shiftTerm (shiftTerm r) := by
    simp only [shiftTerm,Term.subst_subst,Term.subst,swapBinders]
  change Structural (.par (.newVar (a.rename (Option.map some))) (.active none (shiftTerm r)))
    (.newVar (.par ((a.rename some).rename swapBinders)
      (.active (some none) ((shiftTerm (shiftTerm r)).subst (fun v => .var (swapBinders v))))))
  rw [ha,hr]
  exact (Structural.comm _ _).trans ((Structural.newPar _ _).trans
    (.newVar (Structural.comm _ _)))

/-- Close an old local while preserving the genuinely fresh observer outside
it. Scope's binder exchange is derived by an injective coordinate permutation. -/
theorem CapturedEq.scope {a : Extended (Option V)} {r s : Term V}
    (h : CapturedEq a (shiftTerm r) (shiftTerm s)) : CapturedEq (.newVar a) r s :=
  (captureFrame_scope a r).trans
    ((Structural.newVar (h.rename swapBinders swapBinders_involutive.injective)).trans
      (captureFrame_scope a s).symm)

theorem CapturedEq.closeVars (n : Nat) (f : Extended (LocalVars n V)) (r s : Term V)
    (h : CapturedEq f (r.subst (fun v => .var (outerVar n v)))
      (s.subst (fun v => .var (outerVar n v)))) : CapturedEq (Extended.closeVars n f) r s := by
  induction n generalizing V with
  | zero =>
    change CapturedEq f (r.subst Term.var) (s.subst Term.var) at h
    change CapturedEq f r s
    exact (congrArg₂ (CapturedEq f) (Term.subst_var r) (Term.subst_var s)).mp h
  | succ n ih =>
    have hh : CapturedEq f ((shiftTerm r).subst (fun v => .var (outerVar n v)))
        ((shiftTerm s).subst (fun v => .var (outerVar n v))) := by
      simpa only [shiftTerm,Term.subst_subst,Term.subst,outerVar] using h
    exact (ih f (shiftTerm r) (shiftTerm s) hh).scope

/-- A satisfying assignment distinguishes captures using the original full-E
constraints. This is a consequence of the actual path, not its definition. -/
theorem CapturedEq.sound {f : Extended V} {r s : Term V} (h : CapturedEq f r s)
    {env : V → Ground} (hf : f.Satisfies env) : EqE (r.subst env) (s.subst env) := by
  have hl : (captureFrame f r).Satisfies (extendEnv env (r.subst env)) := by
    refine ⟨(satisfies_rename f some _).mpr hf,?_⟩
    simpa only [Satisfies,shiftTerm_eval,extendEnv] using EqE.refl (r.subst env)
  have hr := (Structural.satisfies h _).mp hl
  simpa only [captureFrame,Satisfies,shiftTerm_eval,extendEnv] using hr.2

/-- Its equivalence laws are proofs in the original source calculus. -/
def capturedSetoid (f : Extended V) : Setoid (Term V) where
  r := CapturedEq f
  iseqv := ⟨CapturedEq.refl f,CapturedEq.symm,CapturedEq.trans⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
