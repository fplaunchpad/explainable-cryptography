import ExplainableCrypto.Helios.Symbolic.SourceCapturedEquations

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V W : Type}

/-- The carrier equality is exactly an original structural equality of fresh
captures in this fixed frame. All algebra laws are supplied by checked paths. -/
noncomputable def captureAlgebra (f : Extended V) : FrameAlgebra :=
  FrameAlgebra.ofTermCongruence (capturedSetoid f) (CapturedEq.of_eqE f) (CapturedEq.subst_congr f)

theorem captureAlgebra_eval (f : Extended V) (env : W → Term V) (t : Term W) :
    (captureAlgebra f).eval (fun v => Quotient.mk (capturedSetoid f) (env v)) t =
      Quotient.mk (capturedSetoid f) (t.subst env) :=
  FrameAlgebra.ofTermCongruence_eval _ (CapturedEq.of_eqE f) (CapturedEq.subst_congr f) env t

theorem captureAlgebra_eval_vars (f : Extended V) (t : Term V) :
    (captureAlgebra f).eval (fun v => Quotient.mk (capturedSetoid f) (.var v)) t =
      Quotient.mk (capturedSetoid f) t := by
  simpa only [Term.subst_var] using captureAlgebra_eval f Term.var t

theorem captureAlgebra_groundValue (f : Extended V) (m : Ground) :
    (captureAlgebra f).groundValue m = Quotient.mk (capturedSetoid f) (groundTerm m) := by
  apply congrArg (Quotient.mk (capturedSetoid f))
  apply congrArg m.subst
  funext v
  exact v.elim

/-- Every active leaf supplies its own equation to the fixed containing frame.
Parallel weakening derives the premise for each subtree. -/
theorem FrameForest.model_of_captured {f : Extended V} (hf : f.FrameForest)
    (M : FrameAlgebra) (env : V → M.Value)
    (he : ∀ r s, CapturedEq f r s → M.eval env r = M.eval env s) : M.Satisfies f env := by
  induction f with
  | plain => trivial
  | newVar => exact hf.elim
  | active x m => exact (M.eval_var env x).symm.trans (he _ _ (CapturedEq.provider x m))
  | par a b ih ij =>
    exact ⟨ih hf.1 env (fun r s h => he r s (h.parLeft b)),
      ij hf.2 env (fun r s h => he r s (h.parRight a))⟩

/-- No model witness is assumed: the actual provider equations establish the
identity-variable assignment in the structural capture quotient. -/
theorem FrameForest.captureAlgebra_satisfies {f : Extended V} (hf : f.FrameForest) :
    (captureAlgebra f).Satisfies f (fun v => Quotient.mk (capturedSetoid f) (.var v)) := by
  apply hf.model_of_captured
  intro r s h
  rw [captureAlgebra_eval_vars,captureAlgebra_eval_vars]
  exact Quotient.sound h

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended

namespace ExplainableCrypto.Helios.Symbolic.FrameAlgebra
open Historical.General.Source
variable (M : FrameAlgebra) {V : Type}

/-- A complete assignment to the extracted forest supplies actual witnesses
for every original local binder, in the exact outerVar coordinates. -/
theorem satisfies_closeVars (n : Nat) (f : Extended (Extended.LocalVars n V))
    (env : Extended.LocalVars n V → M.Value) (h : M.Satisfies f env) :
    M.Satisfies (Extended.closeVars n f) (fun v => env (Extended.outerVar n v)) := by
  induction n generalizing V with
  | zero => exact h
  | succ n ih =>
    have ht := ih f env h
    refine ⟨env (Extended.outerVar n none),?_⟩
    have he : M.extend (fun v => env (Extended.outerVar (n+1) v))
        (env (Extended.outerVar n none)) = (fun v => env (Extended.outerVar n v)) := by
      funext v
      cases v <;> rfl
    simpa only [he] using ht

end ExplainableCrypto.Helios.Symbolic.FrameAlgebra

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {handles : Nat} {r hidden : Finset Nat}

/-- Derive an actual structural equality of the fresh output variable and a
ground capture. Forest extraction, the quotient laws and its satisfying model
are all constructed here. Converting this equality to the full target frame
still requires the fresh-copy and reclosure bridge. -/
theorem BoundOutput.opened_capture_ground {a : Named (Fin handles)}
    {b : Named (Option (Fin handles))} {c : Nat} {φ : Frame r handles}
    (h : BoundOutput a c b) (hp : a.RepresentsFrame hidden φ)
    {ρ : NameAssignment} {ns : List SourceName} {d : Extended (Option (Fin handles))}
    (ho : Opens b ρ ns d) :
    ∃ m : Ground, Extended.CapturedEq d.frameOf (.var none) (Extended.groundTerm m) := by
  obtain ⟨f,m,_,hall⟩ := h.opened_algebra_values hp ho
  obtain ⟨n,q,hq,hs⟩ := d.exists_variable_frame_prefix
  let M := Extended.captureAlgebra q
  let env : Extended.LocalVars n (Option (Fin handles)) → M.Value :=
    fun v => Quotient.mk (Extended.capturedSetoid q) (.var v)
  have hm := M.satisfies_closeVars n q env hq.captureAlgebra_satisfies
  have hd := (M.satisfies_frameOf d _).mp ((M.structural_satisfies hs _).mpr hm)
  have he : (fun v => env (Extended.outerVar n v)) =
      M.extend (fun v => env (Extended.outerVar n (some v))) (env (Extended.outerVar n none)) := by
    funext v
    cases v <;> rfl
  rw [he] at hd
  have hv := (hall M _ _ hd).2
  have hv' : Extended.CapturedEq q (.var (Extended.outerVar n none)) (Extended.groundTerm m) := by
    exact Quotient.exact (s := Extended.capturedSetoid q)
      (hv.trans (Extended.captureAlgebra_groundValue q m))
  have hc := Extended.CapturedEq.closeVars n q (.var none) (Extended.groundTerm m)
    (by simpa only [Term.subst,Extended.groundTerm_subst] using hv')
  exact ⟨m,hc.frame_structural hs.symm⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
