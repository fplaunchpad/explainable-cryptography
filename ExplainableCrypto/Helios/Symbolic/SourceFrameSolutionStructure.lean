import ExplainableCrypto.Helios.Symbolic.SourceNamedFrameSolutions

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

theorem models_nameComm (a : Named V) (n m : SourceName) (ρ : Nat → Nat) (env : V → Ground) :
    (newName n (newName m a)).Models ρ env ↔ (newName m (newName n a)).Models ρ env := by
  cases n with
  | channel n => cases m <;> rfl
  | base n =>
    cases m with
    | channel m => rfl
    | base m =>
      by_cases he : n=m
      · subst m; rfl
      · simp only [Models]
        constructor
        · rintro ⟨x,y,h⟩
          refine ⟨y,x,?_⟩
          rwa [Function.update_comm he] at h
        · rintro ⟨y,x,h⟩
          refine ⟨x,y,?_⟩
          rwa [Function.update_comm he]

theorem models_alphaBase (a : Named V) (n m : Nat) (ρ : Nat → Nat) (env : V → Ground)
    (hf : SourceName.base m ∉ a.allNames) :
    (newName (.base n) a).Models ρ env ↔
      (newName (.base m) (a.mapNames (Equiv.swap n m) id)).Models ρ env := by
  change (∃ k, a.Models (Function.update ρ n k) env) ↔
    ∃ k, (a.mapNames (Equiv.swap n m) (Equiv.refl Nat)).Models (Function.update ρ m k) env
  apply exists_congr
  intro k
  rw [models_mapNames]
  apply models_names_congr
  intro x hx
  have hm : x ≠ m := fun he => hf (he ▸ freeNames_subset_allNames a hx)
  by_cases hn : x=n
  · subst x
    simp
  · simp [Equiv.swap_apply_of_ne_of_ne hn hm,hn,hm]

/-- Every actual source structural derivation preserves the complete set of
frame-equation solutions, including alpha, name extrusion and both Subst cases. -/
theorem Structural.models {a b : Named V} (h : Structural a b)
    (ρ : Nat → Nat) (env : V → Ground) : a.Models ρ env ↔ b.Models ρ env := by
  induction h generalizing ρ with
  | refl => rfl
  | symm h ih => exact (ih _ _).symm
  | trans h h' ih ih' => exact (ih _ _).trans (ih' _ _)
  | embed h => exact (h.mapNames ρ id).satisfies env
  | parLeft c h ih => exact and_congr (ih _ _) Iff.rfl
  | parRight a h ih => exact and_congr Iff.rfl (ih _ _)
  | newName n h ih => cases n <;> simp only [Models,ih]
  | newVar h ih => exact exists_congr (fun m => ih _ _)
  | embedPar => rfl
  | embedVar => rfl
  | zero => simp only [Models,Extended.mapNames,Extended.Satisfies,and_true]
  | assoc => exact and_assoc
  | comm => exact and_comm
  | nameZero n => cases n <;> simp only [Models,Extended.mapNames,Extended.Satisfies,exists_const]
  | nameComm n m a => exact models_nameComm a n m ρ env
  | nameVarComm n a =>
    cases n with
    | base n => exact exists_comm
    | channel n => rfl
  | varComm a =>
    simp only [Models,models_rename,Extended.extendEnv_swapBinders]
    exact exists_comm
  | namePar a n b hf =>
    cases n with
    | channel n => rfl
    | base n =>
      simp only [Models,models_update_unused a ρ env n _ hf,exists_and_left]
  | varPar a b =>
    simp only [Models,models_rename,extendEnv,exists_and_left]
  | alphaBase a n m hf => exact models_alphaBase a n m ρ env hf
  | alphaChannel a n m hf =>
    exact (models_mapNames a (Equiv.refl Nat) (Equiv.swap n m) ρ env).symm

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
