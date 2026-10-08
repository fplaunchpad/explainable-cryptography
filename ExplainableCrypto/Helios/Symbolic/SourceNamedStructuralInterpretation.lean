import ExplainableCrypto.Helios.Symbolic.SourceBodyInterpretationContexts

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- Every source structural rule preserves the full interpreted frame and body.
Assignments may identify names; operational correspondence requires additional
freshness conditions and does not follow from this statement. -/
theorem Structural.interprets {a b : Named V} (h : Structural a b)
    (ρ : NameAssignment) (env : V → Ground) (p : Agent Empty) :
    a.Interprets ρ env p ↔ b.Interprets ρ env p := by
  induction h generalizing ρ p with
  | refl => rfl
  | symm h ih => exact (ih _ _ _).symm
  | trans h h' ih ih' => exact (ih _ _ _).trans (ih' _ _ _)
  | embed h => exact (h.mapNames ρ.base ρ.channel).realizes env p
  | parLeft c h ih => simp only [Interprets,ih]
  | parRight a h ih => simp only [Interprets,ih]
  | newName n h ih => simp only [Interprets,ih]
  | newVar h ih => simp only [Interprets,ih]
  | embedPar => rfl
  | embedVar => rfl
  | zero a => exact interprets_zero a ρ env p
  | assoc a b c => exact interprets_assoc a b c ρ env p
  | comm a b => exact interprets_comm a b ρ env p
  | nameZero n =>
    simp only [Interprets,Extended.mapNames,Agent.mapNames,Extended.Realizes,
      Agent.subst,exists_const]
  | nameComm n m a => exact interprets_nameComm a n m ρ env p
  | nameVarComm n a => exact exists_comm
  | varComm a =>
    simp only [Interprets,interprets_rename,Extended.extendEnv_swapBinders]
    exact exists_comm
  | namePar a n b hf => exact interprets_namePar a b n hf ρ env p
  | varPar a b => exact interprets_varPar a b ρ env p
  | alphaBase a n m hf =>
    exact interprets_alpha a (.base n) (.base m) (Equiv.swap n m) (Equiv.refl Nat)
      (SourceName.map_base_swap_eq n m) hf ρ env p
  | alphaChannel a n m hf =>
    exact interprets_alpha a (.channel n) (.channel m) (Equiv.refl Nat) (Equiv.swap n m)
      (SourceName.map_channel_swap_eq n m) hf ρ env p

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
