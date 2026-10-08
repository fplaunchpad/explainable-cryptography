import ExplainableCrypto.Helios.Symbolic.SourceExtendedSyntax

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V : Type}

/-- Removing an unused fresh binder restores the complete process, including
all of its nested input binders. -/
theorem Agent.shift_bind (p : Agent V) (m : Term V) : p.shift.bind m = p := by
  simp only [Agent.shift,Agent.bind,Agent.subst_subst]
  simpa only [Term.subst,inputSubst] using p.subst_var

/-- Subst under a fresh active let agrees with binding and reinserting its
now-unused variable. The active substitution never captures an outer variable. -/
theorem Agent.replace_fresh (p : Agent (Option V)) (m : Term V) :
    p.subst (replaceVar none (shiftTerm m)) = (p.bind m).shift := by
  classical
  simp only [Agent.shift,Agent.bind,Agent.subst_subst]
  congr 1
  funext v
  cases v <;> simp [replaceVar,inputSubst,shiftTerm,Term.subst]

/-- An atomic relay followed by evaluation of its active variable performs
exactly the original input substitution, also beneath further binders. -/
theorem Agent.atomic_relay_bind (q : Agent (Option V)) (m : Term V) :
    ((q.subst (liftSubst (fun v => .var (some v)))).bind (.var none)).bind m = q.bind m := by
  simp only [Agent.bind,Agent.subst_subst]
  congr 1
  funext v
  cases v <;> simp [liftSubst,inputSubst,Term.subst]

namespace Extended
/-- Explicit let elimination: Subst, fresh New-Par, Alias and Par-0. -/
theorem let_eliminate (m : Term V) (p : Agent (Option V)) :
    Structural (letTerm m p) (.plain (p.bind m)) := by
  have h₁ := Structural.newVar (Structural.substPlain none (shiftTerm m) p)
  rw [Agent.replace_fresh] at h₁
  have h₂ := Structural.newVar (Structural.comm (.active none (shiftTerm m)) (.plain (p.bind m).shift))
  have h₃ := (Structural.newPar (.plain (p.bind m)) (.active none (shiftTerm m))).symm
  have h₄ := Structural.parRight (.plain (p.bind m)) (Structural.alias m)
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (Structural.zero _))))

/-- Factoring an arbitrary output message into a fresh active variable is a
derived structural equivalence, not a new primitive output rule. -/
theorem output_factor (c : Nat) (m : Term V) (p : Agent V) :
    Structural (.plain (.output c m p)) (letTerm m (.output c (.var none) p.shift)) := by
  have h := let_eliminate m (.output c (.var none) p.shift)
  change Structural _ (.plain (.output c m (p.shift.bind m))) at h
  rw [Agent.shift_bind] at h
  exact h.symm

/-- Figure 3 atomic Comm and its active-let context derive full message
communication. Both continuations, and the message itself, are arbitrary. -/
theorem message_communication (c : Nat) (m : Term V) (p : Agent V) (q : Agent (Option V)) :
    Reduction (.plain (.par (.output c m p) (.input c q))) (.plain (.par p (q.bind m))) := by
  let before : Agent (Option V) := .par (.output c (.var none) p.shift) ((Agent.input c q).shift)
  let after : Agent (Option V) := .par p.shift ((q.subst (liftSubst (fun v => .var (some v)))).bind (.var none))
  have hb : before.bind m = .par (.output c m p) (.input c q) := by
    change Agent.par (.output c m (p.shift.bind m)) ((Agent.input c q).shift.bind m) = _
    rw [Agent.shift_bind,Agent.shift_bind]
  have ha : after.bind m = .par p (q.bind m) := by
    change Agent.par (p.shift.bind m) (((q.subst (liftSubst (fun v => .var (some v)))).bind (.var none)).bind m) = _
    rw [Agent.shift_bind,Agent.atomic_relay_bind]
  have hbefore := (let_eliminate m before).symm
  rw [hb] at hbefore
  have hafter := let_eliminate m after
  rw [ha] at hafter
  apply Reduction.congr hbefore ?_ hafter
  exact .newVar (.parRight _ (.atomComm c none p.shift (q.subst (liftSubst (fun v => .var (some v))))))

/-- Parallel context lifting through the two syntactic plain/extended forms. -/
theorem Reduction.plain_parLeft {p p' : Agent V} (q : Agent V)
    (h : Reduction (.plain p) (.plain p')) :
    Reduction (.plain (.par p q)) (.plain (.par p' q)) :=
  .congr (.plainPar _ _) (.parLeft _ h) (Structural.plainPar _ _).symm

theorem Reduction.plain_parRight (p : Agent V) {q q' : Agent V}
    (h : Reduction (.plain q) (.plain q')) :
    Reduction (.plain (.par p q)) (.plain (.par p q')) :=
  .congr (.plainPar _ _) (.parRight _ h) (Structural.plainPar _ _).symm

/-- Every direct evaluated core reduction is derivable in the explicit
variable/active fragment, including ground semantic conditionals and contexts. -/
theorem coreStep_derivable {p q : Agent Empty} (h : Agent.CoreStep p q) :
    Reduction (.plain p) (.plain q) := by
  induction h with
  | comm c m p q => exact message_communication c m p q
  | thenBranch f p q hf =>
    have he : (Empty.elim : Empty → Term Empty) = Term.var := by funext v; exact v.elim
    simpa only [he,Formula.subst_var] using Reduction.thenBranch f p q hf
  | elseBranch f p q hf =>
    have he : (Empty.elim : Empty → Term Empty) = Term.var := by funext v; exact v.elim
    simpa only [he,Formula.subst_var] using Reduction.elseBranch f p q hf
  | parLeft q _ ih => exact ih.plain_parLeft q
  | parRight p _ ih => exact ih.plain_parRight p
end Extended
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
