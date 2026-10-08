import ExplainableCrypto.Helios.Symbolic.SourceLocalNormalization

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

/-- A finite sequence of source term lets ending in one complete result.
Each let binds None and shifts all older variables through Some. -/
inductive TermProgram : Type → Type 1 where
  | result : Term V → TermProgram V
  | letTerm : Term V → TermProgram (Option V) → TermProgram V

namespace TermProgram
variable {V W : Type}

def value : {V : Type} → TermProgram V → Term V
  | _, .result m => m
  | _, .letTerm m p => bindInput p.value m

def eval : {V W : Type} → (V → Term W) → TermProgram V → Term W
  | _, _, σ, .result m => m.subst σ
  | _, _, σ, .letTerm m p => p.eval (extendEnv σ (m.subst σ))

def bindings : {V : Type} → TermProgram V → Nat
  | _, .result _ => 0
  | _, .letTerm _ p => 1 + p.bindings

/-- Every source let becomes a restricted active provider and its actual
continuation. The sole public operation sends the program's final result. -/
def compile (channel : Nat) : {V : Type} → TermProgram V → Extended V
  | _, .result m => .plain (.output channel m .nil)
  | _, .letTerm m p => .newVar (.par (.active none (shiftTerm m)) (p.compile channel))

theorem eval_value (p : TermProgram V) (σ : V → Term W) : p.eval σ = p.value.subst σ := by
  induction p generalizing W with
  | result => rfl
  | letTerm m p ih =>
    simp only [eval,value,ih,bindInput_eval]

theorem eval_var (p : TermProgram V) : p.eval Term.var = p.value := by
  rw [eval_value,Term.subst_var]

/-- The entire let sequence eliminates by actual source structural rules,
leaving exactly one output of the complete computed term. -/
theorem compile_normalizes (p : TermProgram V) (channel : Nat) :
    Extended.Structural (p.compile channel) (.plain (.output channel p.value .nil)) := by
  induction p with
  | result => exact .refl _
  | letTerm m p ih =>
    exact (Extended.Structural.newVar (Extended.Structural.parRight _ ih)).trans
      (Extended.let_eliminate m (.output channel p.value .nil))

theorem compile_no_exports (p : TermProgram V) (channel : Nat) (v : V) :
    ¬ (p.compile channel).Exports v := by
  intro h
  exact (p.compile_normalizes channel).exports v |>.mp h

end TermProgram
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
