import ExplainableCrypto.Helios.Symbolic.SourceAgentProgram

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V W : Type}

/-- A full-E rewrite of one local definition changes every use in the same
continuation, including uses beneath later input binders. -/
theorem Agent.bind_structural {m n : Term V} (h : EqE m n) (p : Agent (Option V)) :
    Extended.Structural (.plain (p.bind m)) (.plain (p.bind n)) :=
  (Extended.let_eliminate m p).symm.trans
    ((Extended.Structural.newVar (Extended.Structural.parLeft _
      (Extended.Structural.rewrite none (h.subst (fun v => .var (some v)))))).trans
        (Extended.let_eliminate n p))

/-- Only one supplied variable value changes; all other values stay literal.
The template abstracts that one value before the fresh let is introduced. -/
theorem Agent.subst_update_structural [DecidableEq V] (p : Agent V) (σ : V → Term W)
    (x : V) {m n : Term W} (h : EqE m n) :
    Extended.Structural (.plain (p.subst (Function.update σ x m)))
      (.plain (p.subst (Function.update σ x n))) := by
  let q := p.subst (fun v => if v=x then .var none else shiftTerm (σ v))
  have hb (t : Term W) : q.bind t = p.subst (Function.update σ x t) := by
    simp only [q,Agent.bind,Agent.subst_subst]
    congr 1
    funext v
    by_cases hv : v=x
    · simp [hv,inputSubst,Term.subst]
    · simp [hv,shiftTerm,Term.subst_subst,Term.subst,inputSubst,Term.subst_var]
  simpa only [hb] using h |> Agent.bind_structural (p := q)

/-- A finite environment of full-E-equal terms induces an actual structural
path between the instantiated processes. This does not assert arbitrary
process EquivE can be lifted underneath every future prefix. -/
theorem Agent.finite_subst_structural [Fintype V] [DecidableEq V] (p : Agent V)
    (σ τ : V → Term W) (h : ∀ v, EqE (σ v) (τ v)) :
    Extended.Structural (.plain (p.subst σ)) (.plain (p.subst τ)) := by
  have hs (s : Finset V) : Extended.Structural (.plain (p.subst σ))
      (.plain (p.subst (fun v => if v ∈ s then τ v else σ v))) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.notMem_empty,ite_false] using Extended.Structural.refl (.plain (p.subst σ))
    | @insert x s hx ih =>
      let env := fun v => if v ∈ s then τ v else σ v
      have hm : Function.update env x (σ x) = env := by
        funext v
        by_cases hv : v=x <;> simp [env,hv,hx]
      have hn : Function.update env x (τ x) = (fun v => if v ∈ insert x s then τ v else σ v) := by
        funext v
        by_cases hv : v=x <;> simp [env,hv]
      exact ih.trans (by simpa only [hm,hn] using p.subst_update_structural env x (h x))
  simpa only [Finset.mem_univ,ite_true] using hs Finset.univ

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
