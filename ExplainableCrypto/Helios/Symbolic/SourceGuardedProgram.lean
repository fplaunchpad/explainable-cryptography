import ExplainableCrypto.Helios.Symbolic.SourceProgramSubstitution
import ExplainableCrypto.Helios.Symbolic.SourceAgentProgram

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

namespace AgentProgram
variable {V W : Type}

def subst : {V W : Type} → (V → Term W) → AgentProgram V → AgentProgram W
  | _, _, σ, .result p => .result (p.subst σ)
  | _, _, σ, .letTerm m p => .letTerm (m.subst σ) (p.subst (liftSubst σ))

theorem value_subst (p : AgentProgram V) (σ : V → Term W) :
    (p.subst σ).value = p.value.subst σ := by
  induction p generalizing W with
  | result => rfl
  | letTerm m p ih => simp only [subst,value,ih,Agent.bind_subst]

end AgentProgram

/-- Construction syntax for the paper's let abbreviations beneath prefixes.
This adds no constructor or action rule to the source calculus. -/
inductive GuardedProgram : Type → Type 1 where
  | plain : Agent V → GuardedProgram V
  | input : Nat → GuardedProgram (Option V) → GuardedProgram V
  | output : Nat → Term V → GuardedProgram V → GuardedProgram V
  | branch : Formula V → GuardedProgram V → GuardedProgram V → GuardedProgram V
  | letTerm : Term V → GuardedProgram (Option V) → GuardedProgram V

namespace GuardedProgram
variable {V W U : Type}

/-- Expand let abbreviations by substitution, preserving every process prefix. -/
def inline : {V : Type} → GuardedProgram V → Agent V
  | _, .plain p => p
  | _, .input c p => .input c p.inline
  | _, .output c m p => .output c m p.inline
  | _, .branch f p q => .branch f p.inline q.inline
  | _, .letTerm m p => p.inline.bind m

def subst : {V W : Type} → (V → Term W) → GuardedProgram V → GuardedProgram W
  | _, _, σ, .plain p => .plain (p.subst σ)
  | _, _, σ, .input c p => .input c (p.subst (liftSubst σ))
  | _, _, σ, .output c m p => .output c (m.subst σ) (p.subst σ)
  | _, _, σ, .branch f p q => .branch (f.subst σ) (p.subst σ) (q.subst σ)
  | _, _, σ, .letTerm m p => .letTerm (m.subst σ) (p.subst (liftSubst σ))

/-- Make head lets explicit as active definitions. Prefix continuations use
inline, since the plain source grammar does not contain extended continuations. -/
def expand : {V : Type} → GuardedProgram V → Extended V
  | _, .letTerm m p => .newVar (.par (.active none (shiftTerm m)) p.expand)
  | _, p => .plain p.inline

def ofProgram : {V : Type} → AgentProgram V → GuardedProgram V
  | _, .result p => .plain p
  | _, .letTerm m p => .letTerm m (ofProgram p)

theorem subst_var (p : GuardedProgram V) : p.subst Term.var = p := by
  induction p <;> simp_all only [subst,Agent.subst_var,Term.subst_var,
    Formula.subst_var,liftSubst_var]

theorem subst_subst (p : GuardedProgram V) (σ : V → Term W) (τ : W → Term U) :
    (p.subst σ).subst τ = p.subst (fun v => (σ v).subst τ) := by
  induction p generalizing W U with
  | plain => simp only [subst,Agent.subst_subst]
  | input c p ih => simp only [subst,ih,funext (liftSubst_comp σ τ)]
  | output c m p ih => simp only [subst,Term.subst_subst,ih]
  | branch f p q ih ih' => simp only [subst,Formula.subst_subst,ih,ih']
  | letTerm m p ih => simp only [subst,Term.subst_subst,ih,funext (liftSubst_comp σ τ)]

theorem inline_subst (p : GuardedProgram V) (σ : V → Term W) :
    (p.subst σ).inline = p.inline.subst σ := by
  induction p generalizing W with
  | plain => rfl
  | input c p ih => simp only [subst,inline,Agent.subst,ih]
  | output c m p ih => simp only [subst,inline,Agent.subst,ih]
  | branch f p q ih ih' => simp only [subst,inline,Agent.subst,ih,ih']
  | letTerm m p ih => simp only [subst,inline,ih,Agent.bind_subst]

theorem ofProgram_inline (p : AgentProgram V) : (ofProgram p).inline = p.value := by
  induction p <;> simp_all only [ofProgram,inline,AgentProgram.value]

theorem ofProgram_expand (p : AgentProgram V) : (ofProgram p).expand = p.compile := by
  induction p <;> simp_all only [ofProgram,expand,inline,AgentProgram.compile]

theorem ofProgram_subst (p : AgentProgram V) (σ : V → Term W) :
    (ofProgram p).subst σ = ofProgram (p.subst σ) := by
  induction p generalizing W <;> simp_all only [ofProgram,subst,AgentProgram.subst]

/-- Only head lets use structural closure; no rewrite beneath a prefix is assumed. -/
theorem expand_normalizes (p : GuardedProgram V) :
    Extended.Structural p.expand (.plain p.inline) := by
  induction p with
  | letTerm m p ih =>
    exact (Extended.Structural.newVar (Extended.Structural.parRight _ ih)).trans
      (Extended.let_eliminate m p.inline)
  | plain | input | output | branch => exact .refl _

end GuardedProgram
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
