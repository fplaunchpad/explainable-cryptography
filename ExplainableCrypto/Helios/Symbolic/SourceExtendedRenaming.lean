import ExplainableCrypto.Helios.Symbolic.SourceAtomicOutput

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V W U : Type}

/-- Free variable renaming is the identity at identity, beneath all restrictions. -/
theorem rename_id (a : Extended V) : a.rename id = a := by
  induction a with
  | plain p => exact congrArg Extended.plain p.subst_var
  | active x m => exact congrArg (Extended.active x) m.subst_var
  | par a b ha hb => simp only [rename,ha,hb]
  | newVar a ha =>
    rename_i V'
    have he : Option.map (id : V' → V') = id := by funext v; cases v <;> rfl
    simpa only [rename,he] using congrArg Extended.newVar ha

/-- Renaming composition retains the entire extended syntax and every active
substitution domain, rather than only renaming its right-hand side. -/
theorem rename_comp (a : Extended V) (f : V → W) (g : W → U) :
    (a.rename f).rename g = a.rename (g ∘ f) := by
  induction a generalizing W U with
  | plain p => simp only [rename,Agent.subst_subst,Term.subst,Function.comp_def]
  | active x m => simp only [rename,Term.subst_subst,Term.subst,Function.comp_def]
  | par a b ha hb => simp only [rename,ha,hb]
  | newVar a ha =>
    simp only [rename,ha]
    congr 2
    funext v
    cases v <;> rfl

/-- Embedding a ground payload introduces no free variables or name changes. -/
def groundTerm (m : Ground) : Term V := m.subst Empty.elim

def groundAgent (p : Agent Empty) : Agent V := p.subst Empty.elim

theorem groundTerm_rename (m : Ground) (f : V → W) :
    (groundTerm m).subst (fun v => .var (f v)) = groundTerm m := by
  simp only [groundTerm,Term.subst_subst]
  congr 1
  funext v
  exact v.elim

theorem groundAgent_rename (p : Agent Empty) (f : V → W) :
    (groundAgent p).subst (fun v => .var (f v)) = groundAgent p := by
  simp only [groundAgent,Agent.subst_subst]
  congr 1
  funext v
  exact v.elim
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
