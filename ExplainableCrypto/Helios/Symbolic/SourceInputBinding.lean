import ExplainableCrypto.Helios.Symbolic.HistoricalProcessMatching

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V W U : Type}

/-- Input adds one fresh local variable. None is the new binder; some v is an
old free variable. The disjoint constructors prevent capture. -/
def liftSubst (σ : V → Term W) : Option V → Term (Option W)
  | none => .var none
  | some v => (σ v).subst (fun w => .var (some w))

/-- Instantiate only the newly bound variable, retaining all previous variables. -/
def inputSubst (message : Term V) : Option V → Term V
  | none => message
  | some v => .var v

/-- Source input substitution is existing term substitution at a fresh binder. -/
def bindInput (body : Term (Option V)) (message : Term V) : Term V :=
  body.subst (inputSubst message)

/-- Generic environment extension models communication and labelled input. -/
def extendEnv (σ : V → Term W) (message : Term W) : Option V → Term W
  | none => message
  | some v => σ v

/-- Bind a symbolic message first, or evaluate it and extend the environment:
both give exactly the same term, without any equation or normalizer. -/
theorem bindInput_eval (body : Term (Option V)) (message : Term V) (σ : V → Term W) :
    (bindInput body message).subst σ = body.subst (extendEnv σ (message.subst σ)) := by
  simp only [bindInput,Term.subst_subst]
  congr 1
  funext v
  cases v <;> rfl

/-- Substitution under a binder preserves the newly bound variable. -/
theorem liftSubst_comp (σ : V → Term W) (τ : W → Term U) (v : Option V) :
    ((liftSubst σ) v).subst (liftSubst τ) = liftSubst (fun x => (σ x).subst τ) v := by
  cases v with
  | none => rfl
  | some v => simp only [liftSubst,Term.subst_subst,Term.subst]

theorem bindInput_subst (body : Term (Option V)) (message : Term V) (σ : V → Term W) :
    bindInput (body.subst (liftSubst σ)) (message.subst σ) = (bindInput body message).subst σ := by
  rw [bindInput_eval]
  simp only [bindInput,Term.subst_subst]
  congr 1
  funext v
  cases v with
  | none => rfl
  | some v => simp only [liftSubst,inputSubst,extendEnv,Term.subst_subst,Term.subst,Term.subst_var]

/-- Renaming the previous private variables cannot change a bound evaluation.
The fresh binder remains None; its payload may contain the old variables. -/
theorem bindInput_rename (e : V ≃ W) (body : Term (Option V)) (message : Term V) :
    bindInput (body.subst (fun v => .var (v.map e))) (message.subst (fun v => .var (e v))) =
      (bindInput body message).subst (fun v => .var (e v)) := by
  have h : (fun v => Term.var (v.map e)) = liftSubst (fun v => .var (e v)) := by
    funext v
    cases v <;> rfl
  rw [h]
  exact bindInput_subst body message _

/-- A public symbolic message and body remain public when the input is bound. -/
theorem bindInput_public (restricted : Finset Nat) (body : Term (Option V)) (message : Term V)
    (hb : body.Public restricted) (hm : message.Public restricted) :
    (bindInput body message).Public restricted := by
  exact Term.Public.subst body _ hb (fun v => by cases v; exact hm; trivial)

/-- Split public handles from private input locals. An accepted local can be
flattened to its original public recipe; no public handle is renamed. -/
def flattenLocals {handles : Nat} (locals : V → Recipe handles) : Fin handles ⊕ V → Recipe handles :=
  Sum.elim Term.var locals

theorem flattenLocals_eval {handles : Nat} {restricted : Finset Nat}
    (φ : Frame restricted handles) (locals : V → Recipe handles) (body : Term (Fin handles ⊕ V)) :
    φ.eval (body.subst (flattenLocals locals)) =
      body.subst (Sum.elim φ.value (fun v => φ.eval (locals v))) := by
  simp only [Frame.eval,Term.subst_subst]
  congr 1
  funext v
  cases v <;> rfl

theorem flattenLocals_public {handles : Nat} (restricted : Finset Nat)
    (locals : V → Recipe handles) (body : Term (Fin handles ⊕ V))
    (hp : ∀ v, (locals v).Public restricted) (hb : body.Public restricted) :
    (body.subst (flattenLocals locals)).Public restricted :=
  Term.Public.subst body _ hb (fun v => by cases v; trivial; exact hp _)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
