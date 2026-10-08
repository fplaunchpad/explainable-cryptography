import ExplainableCrypto.Helios.Symbolic.SourceProgramSubstitution

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V W : Type}

namespace Named

/-- Exact variable instantiation through named syntax. Name binders require
freshness for every supplied full term; active domains still map to variables.
This is a substitution graph, not a new source structural or action rule. -/
inductive Instantiates : {V W : Type} → (V → Term W) → Named V → Named W → Prop where
  | embed {V W : Type} {σ : V → Term W} {a : Extended V} {b : Extended W} :
      Extended.Instantiates σ a b → Instantiates σ (.embed a) (.embed b)
  | par {V W : Type} {σ : V → Term W} {a b : Named V} {a' b' : Named W} :
      Instantiates σ a a' → Instantiates σ b b' → Instantiates σ (.par a b) (.par a' b')
  | newVar {V W : Type} {σ : V → Term W} {a : Named (Option V)} {b : Named (Option W)} :
      Instantiates (liftSubst σ) a b → Instantiates σ (.newVar a) (.newVar b)
  | newName {V W : Type} {σ : V → Term W} (n : SourceName) {a : Named V} {b : Named W}
      (hf : ∀ v, n ∉ (σ v).nameSupport.image SourceName.base) :
      Instantiates σ a b → Instantiates σ (.newName n a) (.newName n b)

theorem Instantiates.unique {σ : V → Term W} {a : Named V} {b c : Named W}
    (h : Instantiates σ a b) (k : Instantiates σ a c) : b = c := by
  induction h with
  | embed h => cases k with | embed hk => rw [h.unique hk]
  | par _ _ ha hb => cases k with | par ka kb => rw [ha ka,hb kb]
  | newVar _ ih => cases k with | newVar hk => rw [ih hk]
  | newName n hf _ ih => cases k with | newName _ _ hk => rw [ih hk]

/-- Variable renaming introduces no literal names and always respects name
binders. Domain renaming is certified by the existing Extended graph. -/
theorem instantiates_rename (a : Named V) (σ : V → W) :
    Instantiates (fun v => .var (σ v)) a (a.rename σ) := by
  induction a generalizing W with
  | embed a => exact .embed (Extended.instantiates_rename a σ)
  | par a b ha hb => exact .par (ha σ) (hb σ)
  | newName n a ih => exact .newName n (by simp [Term.nameSupport]) (ih σ)
  | newVar a ih =>
    apply Instantiates.newVar
    simpa only [liftSubst_rename] using ih (Option.map σ)

end Named

namespace ScopedTermProgram

/-- Freshness of a substitution is preserved beneath a local variable
binder: None is new, while older supplied values are shifted through Some. -/
theorem freshFor_lift (p : ScopedTermProgram (Option V)) (σ : V → Term W)
    (hf : ∀ n ∈ p.names, ∀ v, n ∉ (σ v).nameSupport) : p.FreshFor (liftSubst σ) := by
  intro n hn v
  cases v with
  | none => exact Finset.notMem_empty _
  | some v => simpa only [liftSubst,Term.nameSupport_rename] using hf n hn v

/-- Compile the open program and instantiate its actual source syntax, or
substitute the program and compile it: the exact graph certifies agreement. -/
theorem compile_instantiates (p : ScopedTermProgram V) (σ : V → Term W) (channel : Nat)
    (hf : p.FreshFor σ) : Named.Instantiates σ (p.compile channel) ((p.subst σ).compile channel) := by
  induction p generalizing W with
  | result m => exact .embed (.plain σ (.output channel m .nil))
  | letTerm m p ih =>
    have hp := ih (liftSubst σ) (freshFor_lift p σ hf)
    have ha := Extended.Instantiates.active (liftSubst σ) none none (shiftTerm m) rfl
    apply Named.Instantiates.newVar
    apply Named.Instantiates.par ?_ hp
    apply Named.Instantiates.embed
    simpa only [shiftTerm_subst] using ha
  | newName n p ih =>
    apply Named.Instantiates.newName (.base n)
    · intro v
      simpa using hf n (by simp [names]) v
    · exact ih σ (fun m hm v => hf m (by simp [names,hm]) v)

end ScopedTermProgram
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
