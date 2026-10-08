import ExplainableCrypto.Helios.Symbolic.SourceFrameConstraints

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V W : Type}

/-- Proof instrumentation for frame equations. A restricted base name ranges
over atoms; a restricted variable ranges over full ground terms. Assignments
may collide. Observations below must quantify over every solution. -/
def Models : {V : Type} → Named V → (Nat → Nat) → (V → Ground) → Prop
  | _, .embed a, ρ, env => (a.mapNames ρ id).Satisfies env
  | _, .par a b, ρ, env => a.Models ρ env ∧ b.Models ρ env
  | _, .newName (.base n) a, ρ, env => ∃ k : Nat, a.Models (Function.update ρ n k) env
  | _, .newName (.channel _) a, ρ, env => a.Models ρ env
  | _, .newVar a, ρ, env => ∃ m : Ground, a.Models ρ (extendEnv env m)

theorem models_names_congr (a : Named V) (ρ τ : Nat → Nat) (env : V → Ground)
    (h : ∀ n, SourceName.base n ∈ a.freeNames → ρ n = τ n) :
    a.Models ρ env ↔ a.Models τ env := by
  induction a generalizing ρ τ with
  | embed a => exact a.satisfies_mapNames_congr ρ τ env h
  | par a b ha hb =>
    exact and_congr (ha _ _ _ (fun n hn => h n (Finset.mem_union_left _ hn)))
      (hb _ _ _ (fun n hn => h n (Finset.mem_union_right _ hn)))
  | newVar a ih => exact exists_congr (fun m => ih _ _ _ h)
  | newName n a ih =>
    cases n with
    | channel c =>
      exact ih _ _ _ (fun n hn => h n (Finset.mem_erase.mpr ⟨by simp,hn⟩))
    | base c =>
      apply exists_congr
      intro k
      apply ih
      intro n hn
      by_cases he : n=c
      · simp [he]
      · simpa only [Function.update_of_ne he] using
          h n (Finset.mem_erase.mpr ⟨by simpa using he,hn⟩)

theorem models_update_unused (a : Named V) (ρ : Nat → Nat) (env : V → Ground)
    (n k : Nat) (hf : SourceName.base n ∉ a.freeNames) :
    a.Models (Function.update ρ n k) env ↔ a.Models ρ env := by
  apply models_names_congr
  intro m hm
  have hmn : m ≠ n := fun he => hf (he ▸ hm)
  exact Function.update_of_ne hmn k ρ

theorem update_comp_equiv (ρ : Nat → Nat) (e : Nat ≃ Nat) (n k : Nat) :
    (Function.update ρ (e n) k) ∘ e = Function.update (ρ ∘ e) n k := by
  funext m
  by_cases he : m=n <;> simp [Function.comp_def,he,e.injective.eq_iff]

theorem models_mapNames (a : Named V) (e k : Nat ≃ Nat) (ρ : Nat → Nat) (env : V → Ground) :
    (a.mapNames e k).Models ρ env ↔ a.Models (ρ ∘ e) env := by
  induction a generalizing ρ with
  | embed a =>
    simp only [mapNames,Models,Extended.mapNames_comp,Function.id_comp]
    exact a.satisfies_mapNames_channels _ _ _
  | par a b ha hb => exact and_congr (ha _ _) (hb _ _)
  | newVar a ih => exact exists_congr (fun m => ih _ _)
  | newName n a ih =>
    cases n with
    | channel c => exact ih _ _
    | base c => simp only [mapNames,SourceName.map,Models,ih,update_comp_equiv]

theorem models_rename (a : Named V) (σ : V → W) (ρ : Nat → Nat) (env : W → Ground) :
    (a.rename σ).Models ρ env ↔ a.Models ρ (fun v => env (σ v)) := by
  induction a generalizing W ρ with
  | embed a => simp only [rename,Models,Extended.mapNames_rename,Extended.satisfies_rename]
  | par a b ha hb => exact and_congr (ha _ _ _) (hb _ _ _)
  | newName n a ih => cases n <;> simp only [rename,Models,ih]
  | newVar a ih =>
    simp only [rename,Models,ih]
    have he (m : Ground) : (fun v => extendEnv env m (Option.map σ v)) =
        extendEnv (fun v => env (σ v)) m := by funext v; cases v <;> rfl
    simp only [he]

theorem models_frameOf (a : Named V) (ρ : Nat → Nat) (env : V → Ground) :
    a.frameOf.Models ρ env ↔ a.Models ρ env := by
  induction a generalizing ρ with
  | embed a => simp only [frameOf,Models,← Extended.frameOf_mapNames,Extended.satisfies_frameOf]
  | par a b ha hb => exact and_congr (ha _ _) (hb _ _)
  | newName n a ih => cases n <;> simp only [frameOf,Models,ih]
  | newVar a ih => exact exists_congr (fun m => ih _ _)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
