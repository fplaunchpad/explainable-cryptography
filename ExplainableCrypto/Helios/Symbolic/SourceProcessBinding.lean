import ExplainableCrypto.Helios.Symbolic.SourceProcessSyntax

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V W U : Type}

theorem liftSubst_var : liftSubst (Term.var : V → Term V) = Term.var := by
  funext v
  cases v <;> rfl

namespace Formula
/-- Static equivalence transports all public source guards, including negative
and conjunctive observations. Neither a syntactic comparator nor a normalizer
is used to decide E. -/
theorem holds_staticEq {restricted : Finset Nat} {handles : Nat}
    {φ ψ : Frame restricted handles} (h : φ.StaticEq ψ)
    (f : Formula (Fin handles)) (hp : f.Public restricted) :
    f.Holds φ.value ↔ f.Holds ψ.value := by
  induction f with
  | equal a b => exact h a b hp.1 hp.2
  | unequal a b => exact not_congr (h a b hp.1 hp.2)
  | both a b ha hb => exact and_congr (ha hp.1) (hb hp.2)

theorem public_subst (f : Formula V) (restricted : Finset Nat) (σ : V → Term W)
    (hf : f.Public restricted) (hσ : ∀ v, (σ v).Public restricted) :
    (f.subst σ).Public restricted := by
  induction f with
  | equal a b => exact ⟨Term.Public.subst a σ hf.1 hσ,Term.Public.subst b σ hf.2 hσ⟩
  | unequal a b => exact ⟨Term.Public.subst a σ hf.1 hσ,Term.Public.subst b σ hf.2 hσ⟩
  | both a b ha hb => exact ⟨ha hf.1,hb hf.2⟩

/-- Flattening input locals preserves the truth of a guard and the public
handle namespace exactly, just as for the message payloads. -/
theorem flattenLocals_holds {restricted : Finset Nat} {handles : Nat}
    (φ : Frame restricted handles) (locals : V → Recipe handles)
    (f : Formula (Fin handles ⊕ V)) :
    (f.subst (flattenLocals locals)).Holds φ.value ↔
      f.Holds (Sum.elim φ.value (fun v => φ.eval (locals v))) := by
  rw [holds_subst]
  have he : (fun v => (flattenLocals locals v).subst φ.value) =
      Sum.elim φ.value (fun v => φ.eval (locals v)) := by
    funext v
    cases v <;> rfl
  rw [he]
end Formula

namespace Agent
@[simp]
theorem subst_var (p : Agent V) : p.subst Term.var = p := by
  induction p with
  | nil => rfl
  | par p q hp hq => simp only [subst,hp,hq]
  | output c m p hp => simp only [subst,Term.subst_var,hp]
  | input c p hp => simp only [subst,liftSubst_var,hp]
  | branch f p q hp hq => simp only [subst,Formula.subst_var,hp,hq]

@[simp]
theorem subst_subst (p : Agent V) (σ : V → Term W) (τ : W → Term U) :
    (p.subst σ).subst τ = p.subst (fun v => (σ v).subst τ) := by
  induction p generalizing W U with
  | nil => rfl
  | par p q hp hq => simp only [subst,hp,hq]
  | output c m p hp => simp only [subst,Term.subst_subst,hp]
  | input c p hp =>
    simp only [subst,hp]
    congr 2
    funext v
    exact liftSubst_comp σ τ v
  | branch f p q hp hq => simp only [subst,Formula.subst_subst,hp,hq]

/-- Instantiation followed by evaluation equals extending the environment. -/
theorem bind_eval (p : Agent (Option V)) (m : Term V) (σ : V → Term W) :
    (p.bind m).subst σ = p.subst (extendEnv σ (m.subst σ)) := by
  simp only [bind,subst_subst]
  congr 1
  funext v
  cases v <;> rfl

/-- Commutation holds for entire continuations, including further inputs. -/
theorem bind_subst (p : Agent (Option V)) (m : Term V) (σ : V → Term W) :
    (p.subst (liftSubst σ)).bind (m.subst σ) = (p.bind m).subst σ := by
  rw [bind_eval]
  simp only [bind,subst_subst]
  congr 1
  funext v
  cases v with
  | none => rfl
  | some v => simp only [liftSubst,inputSubst,extendEnv,Term.subst_subst,Term.subst,Term.subst_var]

theorem bind_rename (e : V ≃ W) (p : Agent (Option V)) (m : Term V) :
    (p.subst (fun v => .var (v.map e))).bind (m.subst (fun v => .var (e v))) =
      (p.bind m).subst (fun v => .var (e v)) := by
  have h : (fun v => Term.var (v.map e)) = liftSubst (fun v => .var (e v)) := by
    funext v
    cases v <;> rfl
  rw [h]
  exact bind_subst p m _

/-- Null and output prefixes cannot internally reduce in isolation. -/
theorem nil_no_coreStep (q : Agent Empty) : ¬ CoreStep .nil q := by
  intro h
  cases h

theorem output_no_coreStep (c : Nat) (m : Ground) (p q : Agent Empty) :
    ¬ CoreStep (.output c m p) q := by
  intro h
  cases h

theorem input_no_coreStep (c : Nat) (p : Agent (Option Empty)) (q : Agent Empty) :
    ¬ CoreStep (.input c p) q := by
  intro h
  cases h

/-- The direct communication rule needs the same static channel and substitutes
exactly the one fresh input binder. Parallel context rules add no extra moves. -/
theorem communication_coreStep_iff (c d : Nat) (m : Ground) (p : Agent Empty)
    (q : Agent (Option Empty)) (r : Agent Empty) :
    CoreStep (.par (.output c m p) (.input d q)) r ↔
      c = d ∧ r = .par p (q.bind m) := by
  constructor
  · intro h
    cases h with
    | comm => exact ⟨rfl,rfl⟩
    | parLeft _ h => exact (output_no_coreStep _ _ _ _ h).elim
    | parRight _ h => exact (input_no_coreStep _ _ _ h).elim
  · rintro ⟨rfl,rfl⟩
    exact .comm _ _ _ _

/-- A direct conditional step chooses exactly a semantically enabled branch. -/
theorem branch_coreStep_iff (f : Formula Empty) (p q r : Agent Empty) :
    CoreStep (.branch f p q) r ↔
      (f.Holds Empty.elim ∧ r = p) ∨ (¬ f.Holds Empty.elim ∧ r = q) := by
  constructor
  · intro h
    cases h with
    | thenBranch _ _ _ h => exact .inl ⟨h,rfl⟩
    | elseBranch _ _ _ h => exact .inr ⟨h,rfl⟩
  · intro h
    rcases h with ⟨h,rfl⟩ | ⟨h,rfl⟩
    · exact .thenBranch _ _ _ h
    · exact .elseBranch _ _ _ h
end Agent
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
