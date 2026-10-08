import ExplainableCrypto.Helios.Symbolic.SourceFrameAlgebra

namespace ExplainableCrypto.Helios.Symbolic.FrameAlgebra
variable {W : Type}

/-- Build the algebra needed by the capture argument from any term congruence
containing full E. The congruence may be relative to a fixed source frame; it
need not be stable under substitution of that frame's own variables. -/
noncomputable def ofTermCongruence (C : Setoid (Term W))
    (he : ∀ {a b : Term W}, EqE a b → C.r a b)
    (hc : ∀ {V : Type} (t : Term V) (σ τ : V → Term W),
      (∀ v, C.r (σ v) (τ v)) → C.r (t.subst σ) (t.subst τ)) : FrameAlgebra where
  Value := Quotient C
  eval env t := Quotient.mk C (t.subst (fun v => (env v).out))
  eval_var env v := Quotient.out_eq (env v)
  eval_subst env t σ := by
    apply Quotient.sound
    rw [Term.subst_subst]
    apply hc t
    intro v
    exact C.symm (Quotient.mk_out _)
  eval_eq := by
    intro V env a b h
    exact Quotient.sound (he (h.subst (fun v => (env v).out)))

/-- Evaluation on a represented environment agrees with literal substitution,
regardless of the representative chosen by Quotient.out. -/
theorem ofTermCongruence_eval (C : Setoid (Term W))
    (he : ∀ {a b : Term W}, EqE a b → C.r a b)
    (hc : ∀ {V : Type} (t : Term V) (σ τ : V → Term W),
      (∀ v, C.r (σ v) (τ v)) → C.r (t.subst σ) (t.subst τ))
    {V : Type} (env : V → Term W) (t : Term V) :
    (ofTermCongruence C he hc).eval (fun v => Quotient.mk C (env v)) t =
      Quotient.mk C (t.subst env) :=
  Quotient.sound (hc t _ _ (fun v => Quotient.mk_out (env v)))

/-- A concrete nontrivial instance uses exactly the existing full-E quotient.
This supplies a control, not the still-required source-capture congruence. -/
noncomputable def fullGround : FrameAlgebra :=
  ofTermCongruence (fullSetoid Empty) (fun h => h) Term.subst_congr

theorem fullGround_eval {V : Type} (env : V → Ground) (t : Term V) :
    fullGround.eval (fun v => (env v).fullClass) t = (t.subst env).fullClass :=
  ofTermCongruence_eval (fullSetoid Empty) (fun h => h) Term.subst_congr env t

theorem fullGround_names_distinct {m n : Nat} (h : m ≠ n) :
    (Term.name m : Ground).fullClass ≠ (Term.name n : Ground).fullClass :=
  fun he => h ((EqE.name_iff m n).mp ((fullClass_eq_iff _ _).mp he))

end ExplainableCrypto.Helios.Symbolic.FrameAlgebra
