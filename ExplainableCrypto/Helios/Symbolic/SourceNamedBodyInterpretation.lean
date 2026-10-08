import ExplainableCrypto.Helios.Symbolic.SourceNameAssignments

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V W : Type}

/-- Full body-and-frame interpretation under assignments of both name sorts.
Name assignments may collide; this relation alone is not an action semantics. -/
def Interprets : {V : Type} → Named V → NameAssignment → (V → Ground) → Agent Empty → Prop
  | _, .embed a, ρ, env, p => (a.mapNames ρ.base ρ.channel).Realizes env p
  | _, .par a b, ρ, env, p =>
      ∃ q r, a.Interprets ρ env q ∧ b.Interprets ρ env r ∧ Agent.EvalEq (.par q r) p
  | _, .newName n a, ρ, env, p => ∃ k : Nat, a.Interprets (Function.update ρ n k) env p
  | _, .newVar a, ρ, env, p => ∃ m : Ground, a.Interprets ρ (extendEnv env m) p

theorem Interprets.congr {a : Named V} {ρ : NameAssignment} {env : V → Ground}
    {p q : Agent Empty} (h : a.Interprets ρ env p) (he : Agent.EvalEq p q) :
    a.Interprets ρ env q := by
  induction a generalizing ρ p q with
  | embed a => exact Extended.Realizes.congr h he
  | par a b ha hb =>
    obtain ⟨r,s,hr,hs,hp⟩ := h
    exact ⟨r,s,hr,hs,hp.trans he⟩
  | newName n a ih =>
    obtain ⟨k,hk⟩ := h
    exact ⟨k,ih hk he⟩
  | newVar a ih =>
    obtain ⟨m,hm⟩ := h
    exact ⟨m,ih hm he⟩

theorem interprets_names_congr (a : Named V) (ρ τ : NameAssignment) (env : V → Ground)
    (p : Agent Empty) (h : ∀ n ∈ a.freeNames, ρ n = τ n) :
    a.Interprets ρ env p ↔ a.Interprets τ env p := by
  induction a generalizing ρ τ p with
  | embed a => rw [Interprets,Interprets,a.mapAssignments_congr ρ τ h]
  | par a b ha hb =>
    have hl (p : Agent Empty) := ha ρ τ env p (fun n hn => h n (Finset.mem_union_left _ hn))
    have hr (p : Agent Empty) := hb ρ τ env p (fun n hn => h n (Finset.mem_union_right _ hn))
    simp only [Interprets,hl,hr]
  | newVar a ih => exact exists_congr (fun m => ih _ _ _ _ h)
  | newName n a ih =>
    apply exists_congr
    intro k
    apply ih
    intro m hm
    by_cases he : m=n
    · simp [he]
    · simpa only [Function.update_of_ne he] using h m (Finset.mem_erase.mpr ⟨he,hm⟩)

theorem interprets_update_unused (a : Named V) (ρ : NameAssignment) (env : V → Ground)
    (p : Agent Empty) (n : SourceName) (k : Nat) (hf : n ∉ a.freeNames) :
    a.Interprets (Function.update ρ n k) env p ↔ a.Interprets ρ env p := by
  apply interprets_names_congr
  intro m hm
  have hmn : m ≠ n := fun he => hf (he ▸ hm)
  exact Function.update_of_ne hmn k ρ

theorem interprets_rename (a : Named V) (σ : V → W) (ρ : NameAssignment)
    (env : W → Ground) (p : Agent Empty) :
    (a.rename σ).Interprets ρ env p ↔ a.Interprets ρ (fun v => env (σ v)) p := by
  induction a generalizing W ρ p with
  | embed a => simp only [rename,Interprets,Extended.mapNames_rename,Extended.realizes_rename]
  | par a b ha hb => simp only [rename,Interprets,ha,hb]
  | newName n a ih => simp only [rename,Interprets,ih]
  | newVar a ih =>
    simp only [rename,Interprets,ih]
    have he (m : Ground) : (fun v => extendEnv env m (Option.map σ v)) =
        extendEnv (fun v => env (σ v)) m := by funext v; cases v <;> rfl
    simp only [he]

theorem interprets_mapNames (a : Named V) (e k : Nat ≃ Nat) (ρ : NameAssignment)
    (env : V → Ground) (p : Agent Empty) :
    (a.mapNames e k).Interprets ρ env p ↔ a.Interprets (ρ ∘ SourceName.map e k) env p := by
  induction a generalizing ρ p with
  | embed a =>
    simp only [mapNames,Interprets,Extended.mapNames_comp]
    rfl
  | par a b ha hb => simp only [mapNames,Interprets,ha,hb]
  | newVar a ih => simp only [mapNames,Interprets,ih]
  | newName n a ih => simp only [mapNames,Interprets,ih,NameAssignment.update_comp]

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
