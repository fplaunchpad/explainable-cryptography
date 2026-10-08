import ExplainableCrypto.Helios.Symbolic.SourceComputedVoterElection

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

/-- A finite term computation with explicitly positioned base-name scopes.
Compilation uses the existing Named constructors, not an added source rule. -/
inductive ScopedTermProgram : Type → Type 1 where
  | result : Term V → ScopedTermProgram V
  | letTerm : Term V → ScopedTermProgram (Option V) → ScopedTermProgram V
  | newName : Nat → ScopedTermProgram V → ScopedTermProgram V

namespace ScopedTermProgram
variable {V : Type}

def ofProgram : {V : Type} → TermProgram V → ScopedTermProgram V
  | _, .result m => .result m
  | _, .letTerm m p => .letTerm m (ofProgram p)

def erase : {V : Type} → ScopedTermProgram V → TermProgram V
  | _, .result m => .result m
  | _, .letTerm m p => .letTerm m p.erase
  | _, .newName _ p => p.erase

def names : {V : Type} → ScopedTermProgram V → List Nat
  | _, .result _ => []
  | _, .letTerm _ p => p.names
  | _, .newName n p => n :: p.names

def compile (channel : Nat) : {V : Type} → ScopedTermProgram V → Named V
  | _, .result m => .embed (.plain (.output channel m .nil))
  | _, .letTerm m p => .newVar (.par (.embed (.active none (shiftTerm m))) (p.compile channel))
  | _, .newName n p => .newName (.base n) (p.compile channel)

/-- Every later name scope can cross the current active provider without
capturing any name in its full term. Variable binding uses disjoint Options. -/
def Hoistable : {V : Type} → ScopedTermProgram V → Prop
  | _, .result _ => True
  | _, .letTerm m p => p.Hoistable ∧ ∀ n ∈ p.names, n ∉ m.nameSupport
  | _, .newName _ p => p.Hoistable

theorem erase_ofProgram (p : TermProgram V) : (ofProgram p).erase = p := by
  induction p <;> simp_all only [ofProgram,erase]

theorem names_ofProgram (p : TermProgram V) : (ofProgram p).names = [] := by
  induction p <;> simp_all only [ofProgram,names]

theorem hoistable_ofProgram (p : TermProgram V) : (ofProgram p).Hoistable := by
  induction p with
  | result => trivial
  | letTerm m p ih => exact ⟨ih,by simp [names_ofProgram]⟩

/-- Move the actual nested name scopes to a prefix by New-Par/New-C and
connect the two presentations of variable/parallel contexts. -/
theorem compile_hoist (p : ScopedTermProgram V) (channel : Nat) (hp : p.Hoistable) :
    Named.Structural (p.compile channel)
      (Named.restrictNames (p.names.map SourceName.base) (.embed (p.erase.compile channel))) := by
  induction p with
  | result => exact .refl _
  | newName n p ih => exact .newName (.base n) (ih hp)
  | letTerm m p ih =>
    let a : Named (Option _) := .embed (.active none (shiftTerm m))
    have hf : ∀ u ∈ p.names.map SourceName.base, u ∉ a.freeNames := by
      intro u hu
      obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hu
      simpa only [a,Named.freeNames,Extended.nameSupport,shiftTerm,Term.nameSupport_rename,
        Finset.mem_image,SourceName.base.injEq,exists_eq_right] using hp.2 n hn
    exact (Named.Structural.newVar (Named.Structural.parRight a (ih hp.1))).trans
      ((Named.Structural.newVar (Named.Structural.par_restrictNames_right a _ _ hf)).trans
        ((Named.Structural.var_restrictNames _ _).trans
          (((Named.Structural.newVar (Named.Structural.embedPar _ _).symm).trans
            (Named.Structural.embedVar _).symm).restrictNames _)))

theorem compile_normalizes (p : ScopedTermProgram V) (channel : Nat) (hp : p.Hoistable) :
    Named.Structural (p.compile channel)
      (Named.restrictNames (p.names.map SourceName.base)
        (.embed (.plain (.output channel p.erase.value .nil)))) :=
  (p.compile_hoist channel hp).trans
    ((Named.Structural.embed (p.erase.compile_normalizes channel)).restrictNames _)

end ScopedTermProgram
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
