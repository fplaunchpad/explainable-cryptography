import ExplainableCrypto.Helios.Symbolic.SourceVoterSubstitution

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V W : Type} {n : Nat}

/-- Free key parameter None and free vote parameters Some j are distinct
from the Option binders introduced later by every source term let. -/
def voterTemplateInitial (ns : Names n) (i : Fin 2) : VoterRegisters n (Option (Fin (n+1))) :=
  ⟨.var none,fun j => .name (ns.nonce i j),fun j => .var (some j),
    fun _ => .const .bottom,fun _ => .const .bottom⟩

def voterTemplate (ns : Names n) (i : Fin 2) : ScopedTermProgram (Option (Fin (n+1))) :=
  scopedVoterComponents (ns.nonce i) (List.finRange (n+1)) (voterTemplateInitial ns i)

def voterParameters (ns : Names n) (values : Fin (n+1) → Ground) : Option (Fin (n+1)) → Ground :=
  extendEnv values (publicKey ns)

theorem voterTemplateInitial_apply (ns : Names n) (i : Fin 2) (values : Fin (n+1) → Ground) :
    (voterTemplateInitial ns i).map (voterParameters ns values) = voterInitial ns i values := rfl

/-- Full syntax equality, retaining every local let, name scope and proof
field. The substitution is applied to one fixed open template. -/
theorem voterTemplate_apply (ns : Names n) (i : Fin 2) (values : Fin (n+1) → Ground) :
    (voterTemplate ns i).subst (voterParameters ns values) = scopedVoterProgram ns i values := by
  simp only [voterTemplate,scopedVoterComponents_subst,voterTemplateInitial_apply,scopedVoterProgram]

theorem voterTemplate_freshFor (ns : Names n) (hf : ns.Fresh) (i : Fin 2)
    (values : Fin (n+1) → Ground) (hv : NoncesFreshFor ns values) :
    (voterTemplate ns i).FreshFor (voterParameters ns values) := by
  intro m hm v
  rw [voterTemplate,scopedVoterComponents_names] at hm
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hm
  cases v with
  | none => simpa [voterParameters,extendEnv,publicKey,Term.nameSupport] using (hf.2.2 i j).1
  | some k => exact hv i j k

/-- Actual compiled source instantiation, with name freshness and active-domain
conditions checked by the Named/Extended substitution graphs. -/
theorem voterTemplate_instantiates (ns : Names n) (hf : ns.Fresh) (i : Fin 2)
    (values : Fin (n+1) → Ground) (hv : NoncesFreshFor ns values) (channel : Nat) :
    Named.Instantiates (voterParameters ns values) ((voterTemplate ns i).compile channel)
      ((scopedVoterProgram ns i values).compile channel) := by
  simpa only [voterTemplate_apply] using (voterTemplate ns i).compile_instantiates
    (voterParameters ns values) channel (voterTemplate_freshFor ns hf i values hv)

theorem applied_voter_normalizes (ns : Names n) (hf : ns.Fresh) (i : Fin 2)
    (values : Fin (n+1) → Ground) (hv : NoncesFreshFor ns values) (channel : Nat) :
    Named.Structural (((voterTemplate ns i).subst (voterParameters ns values)).compile channel)
      (Named.restrictNames (voterNonceList ns i)
        (.embed (.plain (.output channel (ballot ns i values) .nil)))) := by
  rw [voterTemplate_apply]
  exact scopedVoterProgram_normalizes ns hf i values hv channel

/-- Variable renaming commutes exactly with compilation into actual Named
syntax, including all variable and name binders. -/
theorem ScopedTermProgram.compile_subst_var (p : ScopedTermProgram V) (σ : V → W) (channel : Nat) :
    (p.subst (fun v => .var (σ v))).compile channel = (p.compile channel).rename σ := by
  induction p generalizing W with
  | result m => rfl
  | newName m p ih => simp only [ScopedTermProgram.subst,ScopedTermProgram.compile,Named.rename,ih]
  | letTerm m p ih =>
    simp only [ScopedTermProgram.subst,ScopedTermProgram.compile,Named.rename,Extended.rename,
      Option.map_none,liftSubst_rename,ih,shiftTerm_rename]

theorem ScopedTermProgram.compile_ground_subst (p : ScopedTermProgram Empty) (channel : Nat) :
    (p.subst (Empty.elim : Empty → Term V)).compile channel = (p.compile channel).rename Empty.elim := by
  have he : (Empty.elim : Empty → Term V) = fun v => .var (Empty.elim v) := by funext v; exact v.elim
  rw [he]
  exact p.compile_subst_var Empty.elim channel

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
