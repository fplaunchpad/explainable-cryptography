import ExplainableCrypto.Helios.Symbolic.SourceScopedElectionActions

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V W U : Type}

namespace TermProgram

def subst : {V W : Type} → (V → Term W) → TermProgram V → TermProgram W
  | _, _, σ, .result m => .result (m.subst σ)
  | _, _, σ, .letTerm m p => .letTerm (m.subst σ) (p.subst (liftSubst σ))

theorem subst_var (p : TermProgram V) : p.subst Term.var = p := by
  induction p <;> simp_all only [subst,Term.subst_var,liftSubst_var]

theorem subst_subst (p : TermProgram V) (σ : V → Term W) (τ : W → Term U) :
    (p.subst σ).subst τ = p.subst (fun v => (σ v).subst τ) := by
  induction p generalizing W U with
  | result => simp only [subst,Term.subst_subst]
  | letTerm m p ih =>
    simp only [subst,Term.subst_subst,ih]
    congr 2
    funext v
    exact liftSubst_comp σ τ v

theorem value_subst (p : TermProgram V) (σ : V → Term W) :
    (p.subst σ).value = p.value.subst σ := by
  induction p generalizing W with
  | result => rfl
  | letTerm m p ih => simp only [subst,value,ih,bindInput_subst]

theorem bindings_subst (p : TermProgram V) (σ : V → Term W) : (p.subst σ).bindings = p.bindings := by
  induction p generalizing W <;> simp_all only [subst,bindings]

end TermProgram

namespace ScopedTermProgram

/-- Syntactic variable substitution; name binders stay literal. Its use as
capture-avoiding source application requires FreshFor below. -/
def subst : {V W : Type} → (V → Term W) → ScopedTermProgram V → ScopedTermProgram W
  | _, _, σ, .result m => .result (m.subst σ)
  | _, _, σ, .letTerm m p => .letTerm (m.subst σ) (p.subst (liftSubst σ))
  | _, _, σ, .newName n p => .newName n (p.subst σ)

def FreshFor (p : ScopedTermProgram V) (σ : V → Term W) : Prop :=
  ∀ n ∈ p.names, ∀ v, n ∉ (σ v).nameSupport

theorem subst_var (p : ScopedTermProgram V) : p.subst Term.var = p := by
  induction p <;> simp_all only [subst,Term.subst_var,liftSubst_var]

theorem subst_subst (p : ScopedTermProgram V) (σ : V → Term W) (τ : W → Term U) :
    (p.subst σ).subst τ = p.subst (fun v => (σ v).subst τ) := by
  induction p generalizing W U with
  | result => simp only [subst,Term.subst_subst]
  | letTerm m p ih =>
    simp only [subst,Term.subst_subst,ih]
    congr 2
    funext v
    exact liftSubst_comp σ τ v
  | newName n p ih => simp only [subst,ih]

theorem names_subst (p : ScopedTermProgram V) (σ : V → Term W) :
    (p.subst σ).names = p.names := by
  induction p generalizing W <;> simp_all only [subst,names]

theorem erase_subst (p : ScopedTermProgram V) (σ : V → Term W) :
    (p.subst σ).erase = p.erase.subst σ := by
  induction p generalizing W <;> simp_all only [subst,erase,TermProgram.subst]

theorem ofProgram_subst (p : TermProgram V) (σ : V → Term W) :
    (ofProgram p).subst σ = ofProgram (p.subst σ) := by
  induction p generalizing W <;> simp_all only [ofProgram,subst,TermProgram.subst]

end ScopedTermProgram
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
