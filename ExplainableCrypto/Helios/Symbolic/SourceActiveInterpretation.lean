import ExplainableCrypto.Helios.Symbolic.SourceEvaluatedEquivalence
import ExplainableCrypto.Helios.Symbolic.SourceExtendedSyntax

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended

/-- An active variable constrains its environment value modulo full E;
restricted variables are existential ground values. The resulting plain
process is observed modulo parallel structure and equational congruence.
This interpretation does not assert existence for arbitrary cyclic constraints. -/
def Realizes : {V : Type} → Extended V → (V → Ground) → Agent Empty → Prop
  | _, .plain p, env, q => Agent.EvalEq (p.subst env) q
  | _, .active x m, env, q => EqE (env x) (m.subst env) ∧ Agent.EvalEq .nil q
  | _, .par a b, env, q => ∃ p r, Realizes a env p ∧ Realizes b env r ∧ Agent.EvalEq (.par p r) q
  | _, .newVar a, env, q => ∃ m : Ground, Realizes a (extendEnv env m) q

variable {V W : Type}

theorem Realizes.congr {a : Extended V} {env : V → Ground} {p q : Agent Empty}
    (h : a.Realizes env p) (he : Agent.EvalEq p q) : a.Realizes env q := by
  induction a with
  | plain => exact h.trans he
  | active => exact ⟨h.1,h.2.trans he⟩
  | par a b ha hb =>
    obtain ⟨r,s,hr,hs,hp⟩ := h
    exact ⟨r,s,hr,hs,hp.trans he⟩
  | newVar a ih =>
    obtain ⟨m,hm⟩ := h
    exact ⟨m,ih hm⟩

theorem realizes_congr_iff (a : Extended V) (env : V → Ground) {p q : Agent Empty}
    (he : Agent.EvalEq p q) : a.Realizes env p ↔ a.Realizes env q :=
  ⟨fun h => h.congr he,fun h => h.congr he.symm⟩

theorem realizes_rename (a : Extended V) (σ : V → W) (env : W → Ground) (p : Agent Empty) :
    (a.rename σ).Realizes env p ↔ a.Realizes (fun v => env (σ v)) p := by
  induction a generalizing W p with
  | plain => simp only [rename,Realizes,Agent.subst_subst,Term.subst]
  | active => simp only [rename,Realizes,Term.subst_subst,Term.subst]
  | par a b ha hb => simp only [rename,Realizes,ha,hb]
  | newVar a ih =>
    simp only [rename,Realizes,ih]
    have he (m : Ground) : (fun v => extendEnv env m (Option.map σ v)) =
        extendEnv (fun v => env (σ v)) m := by funext v; cases v <;> rfl
    simp only [he]

theorem realizes_par (a b : Extended V) (env : V → Ground) {p q : Agent Empty}
    (ha : a.Realizes env p) (hb : b.Realizes env q) :
    (Extended.par a b).Realizes env (.par p q) := ⟨p,q,ha,hb,.refl _⟩

theorem realizes_plain (p : Agent V) (env : V → Ground) :
    (Extended.plain p).Realizes env (p.subst env) := .refl _

theorem realizes_active (x : V) (m : Term V) (env : V → Ground)
    (h : EqE (env x) (m.subst env)) : (Extended.active x m).Realizes env .nil :=
  ⟨h,.refl _⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
