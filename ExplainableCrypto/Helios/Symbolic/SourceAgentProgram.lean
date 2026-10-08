import ExplainableCrypto.Helios.Symbolic.SourceTermProgram

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

/-- Finite local term definitions with an arbitrary plain continuation,
including further input binders, guards and ordered outputs. -/
inductive AgentProgram : Type → Type 1 where
  | result : Agent V → AgentProgram V
  | letTerm : Term V → AgentProgram (Option V) → AgentProgram V

namespace AgentProgram
variable {V W : Type}

def value : {V : Type} → AgentProgram V → Agent V
  | _, .result p => p
  | _, .letTerm m p => p.value.bind m

def eval : {V W : Type} → (V → Term W) → AgentProgram V → Agent W
  | _, _, σ, .result p => p.subst σ
  | _, _, σ, .letTerm m p => p.eval (extendEnv σ (m.subst σ))

def bindings : {V : Type} → AgentProgram V → Nat
  | _, .result _ => 0
  | _, .letTerm _ p => 1 + p.bindings

def compile : {V : Type} → AgentProgram V → Extended V
  | _, .result p => .plain p
  | _, .letTerm m p => .newVar (.par (.active none (shiftTerm m)) p.compile)

theorem eval_value (p : AgentProgram V) (σ : V → Term W) :
    p.eval σ = p.value.subst σ := by
  induction p generalizing W with
  | result => rfl
  | letTerm m p ih => simp only [eval,value,ih,Agent.bind_eval]

theorem eval_var (p : AgentProgram V) : p.eval Term.var = p.value := by
  rw [eval_value,Agent.subst_var]

theorem compile_normalizes (p : AgentProgram V) :
    Extended.Structural p.compile (.plain p.value) := by
  induction p with
  | result => exact .refl _
  | letTerm m p ih =>
    exact (Extended.Structural.newVar (Extended.Structural.parRight _ ih)).trans
      (Extended.let_eliminate m p.value)

theorem compile_no_exports (p : AgentProgram V) (v : V) : ¬ p.compile.Exports v := by
  intro h
  exact (p.compile_normalizes.exports v).mp h

end AgentProgram
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
