import ExplainableCrypto.Helios.Symbolic.SourceExtendedSubstitution

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended

/-- Capture-avoiding substitution in extended syntax. An active domain can
only be mapped to a variable; its full payload is substituted independently.
The relation supports empty target variable types without choosing a default. -/
inductive Instantiates : {V W : Type} → (V → Term W) → Extended V → Extended W → Prop
  | plain {V W : Type} (σ : V → Term W) (p : Agent V) : Instantiates σ (.plain p) (.plain (p.subst σ))
  | active {V W : Type} (σ : V → Term W) (x : V) (y : W) (m : Term V) (h : σ x = .var y) :
      Instantiates σ (.active x m) (.active y (m.subst σ))
  | par {V W : Type} {σ : V → Term W} {a b : Extended V} {a' b' : Extended W} :
      Instantiates σ a a' → Instantiates σ b b' → Instantiates σ (.par a b) (.par a' b')
  | newVar {V W : Type} {σ : V → Term W} {a : Extended (Option V)} {b : Extended (Option W)} :
      Instantiates (liftSubst σ) a b → Instantiates σ (.newVar a) (.newVar b)

variable {V W U : Type}

/-- Domain admissibility suffices to construct the substituted
syntax. Bound local domains map to the fresh variable automatically. -/
theorem instantiates_exists (a : Extended V) (σ : V → Term W)
    (hσ : ∀ x, a.Exports x → ∃ y, σ x = .var y) :
    ∃ b, Instantiates σ a b := by
  induction a generalizing W with
  | plain p => exact ⟨_,.plain σ p⟩
  | active x m =>
    obtain ⟨y,hy⟩ := hσ x rfl
    exact ⟨_,.active σ x y m hy⟩
  | par a b ha hb =>
    obtain ⟨a',ha'⟩ := ha σ (fun x hx => hσ x (.inl hx))
    obtain ⟨b',hb'⟩ := hb σ (fun x hx => hσ x (.inr hx))
    exact ⟨_,.par ha' hb'⟩
  | newVar a ih =>
    obtain ⟨b,hb⟩ := ih (liftSubst σ) (by
      intro x hx
      cases x with
      | none => exact ⟨none,rfl⟩
      | some x =>
        obtain ⟨y,hy⟩ := hσ x hx
        exact ⟨some y,by simp only [liftSubst,hy,Term.subst]⟩)
    exact ⟨_,.newVar hb⟩

theorem Instantiates.unique {σ : V → Term W} {a : Extended V} {b c : Extended W}
    (h : Instantiates σ a b) (k : Instantiates σ a c) : b = c := by
  induction h with
  | plain => cases k; rfl
  | active σ x y m hy =>
    cases k with
    | active _ _ z _ hz =>
      have he : y=z := Term.var.inj (hy.symm.trans hz)
      subst z; rfl
  | par _ _ ha hb => cases k with | par ka kb => rw [ha ka,hb kb]
  | newVar _ ih => cases k with | newVar hk => rw [ih hk]

theorem instantiates_rename (a : Extended V) (σ : V → W) :
    Instantiates (fun v => .var (σ v)) a (a.rename σ) := by
  induction a generalizing W with
  | plain p => exact .plain _ p
  | active x m => exact .active _ x (σ x) m rfl
  | par a b ha hb => exact .par (ha σ) (hb σ)
  | newVar a ih =>
    apply Instantiates.newVar
    simpa only [liftSubst_rename] using ih (Option.map σ)

/-- Composition substitutes both payloads and the surviving variable domains. -/
theorem Instantiates.comp {σ : V → Term W} {τ : W → Term U}
    {a : Extended V} {b : Extended W} {c : Extended U}
    (h : Instantiates σ a b) (k : Instantiates τ b c) :
    Instantiates (fun v => (σ v).subst τ) a c := by
  induction h generalizing U with
  | plain σ p =>
    cases k
    simpa only [Agent.subst_subst] using Instantiates.plain (fun v => (σ v).subst τ) p
  | active σ x y m hy =>
    cases k with
    | active _ _ z _ hz =>
      simpa only [Term.subst_subst] using Instantiates.active (fun v => (σ v).subst τ) x z m
        (by rw [hy]; exact hz)
  | par _ _ ha hb => cases k with | par ka kb => exact .par (ha ka) (hb kb)
  | newVar _ ih =>
    cases k with
    | newVar hk =>
      apply Instantiates.newVar
      simpa only [liftSubst_comp] using ih hk

/-- The existing retained-provider substitution has this same exact syntax
when the surrounding context does not redefine its provider variable. -/
theorem instantiates_substFree (a : Extended V) (x : V) (m : Term V)
    (ha : ¬ a.Exports x) : Instantiates (replaceVar x m) a (a.substFree x m) := by
  classical
  induction a with
  | plain p => exact .plain _ p
  | active y n => exact .active _ y y n (by simp [replaceVar,Ne.symm ha])
  | par a b ihA ihB => exact .par (ihA x m (fun h => ha (.inl h))) (ihB x m (fun h => ha (.inr h)))
  | newVar a ih =>
    apply Instantiates.newVar
    have he : liftSubst (replaceVar x m) = replaceVar (some x) (shiftTerm m) := by
      funext v
      cases v with
      | none => simp [liftSubst,replaceVar]
      | some v =>
        by_cases h : v=x <;> simp [liftSubst,replaceVar,h,shiftTerm,Term.subst]
    rw [he]
    exact ih (some x) (shiftTerm m) ha

/-- The whole substituted context is pinned, not merely its evaluated body. -/
theorem Instantiates.replace_fresh {a : Extended (Option V)} {b : Extended V}
    (m : Term V) (h : Instantiates (inputSubst m) a b) (ha : ¬ a.Exports none) :
    a.substFree none (shiftTerm m) = b.rename some := by
  have hk := h.comp (instantiates_rename b some)
  have he : (fun v => (inputSubst m v).subst (fun w => .var (some w))) = replaceVar none (shiftTerm m) := by
    funext v
    cases v <;> simp [inputSubst,replaceVar,shiftTerm,Term.subst]
  rw [he] at hk
  exact (instantiates_substFree a none (shiftTerm m) ha).unique hk

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
