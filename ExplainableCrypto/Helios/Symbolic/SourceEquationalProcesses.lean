import ExplainableCrypto.Helios.Symbolic.SourceEquationalFormula

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent

/-- Congruence of complete payloads and guards, retaining channels, process
constructors and both continuations. This is not an additional source rule. -/
inductive EquivE : {V : Type} → Agent V → Agent V → Prop where
  | nil : EquivE (.nil : Agent V) .nil
  | par {p p' q q' : Agent V} : EquivE p p' → EquivE q q' → EquivE (.par p q) (.par p' q')
  | output {m m' : Term V} {p p' : Agent V} (c : Nat) :
      EqE m m' → EquivE p p' → EquivE (.output c m p) (.output c m' p')
  | input {p p' : Agent (Option V)} (c : Nat) : EquivE p p' → EquivE (.input c p) (.input c p')
  | branch {f f' : Formula V} {p p' q q' : Agent V} :
      Formula.EquivE f f' → EquivE p p' → EquivE q q' → EquivE (.branch f p q) (.branch f' p' q')

variable {V W : Type}

theorem EquivE.refl (p : Agent V) : EquivE p p := by
  induction p with
  | nil => exact .nil
  | par p q hp hq => exact .par hp hq
  | output c m p hp => exact .output c (.refl _) hp
  | input c p hp => exact .input c hp
  | branch f p q hp hq => exact .branch (.refl f) hp hq

theorem EquivE.symm {p q : Agent V} (h : EquivE p q) : EquivE q p := by
  induction h with
  | nil => exact .nil
  | par h h' ih ih' => exact .par ih ih'
  | output c h h' ih => exact .output c h.symm ih
  | input c h ih => exact .input c ih
  | branch hf h h' ih ih' => exact .branch hf.symm ih ih'

theorem EquivE.trans {p q r : Agent V} (h : EquivE p q) (j : EquivE q r) : EquivE p r := by
  induction h with
  | nil => cases j; exact .nil
  | par h h' ih ih' => cases j with | par k k' => exact .par (ih k) (ih' k')
  | output c hm h ih => cases j with | output _ km k => exact .output c (hm.trans km) (ih k)
  | input c h ih => cases j with | input _ k => exact .input c (ih k)
  | branch hf h h' ih ih' => cases j with | branch kf k k' => exact .branch (hf.trans kf) (ih k) (ih' k')

theorem EquivE.subst {p q : Agent V} (h : EquivE p q) (σ : V → Term W) :
    EquivE (p.subst σ) (q.subst σ) := by
  induction h generalizing W with
  | nil => exact .nil
  | par h h' ih ih' => exact .par (ih σ) (ih' σ)
  | output c hm h ih => exact .output c (hm.subst σ) (ih σ)
  | input c h ih => exact .input c (ih (liftSubst σ))
  | branch hf h h' ih ih' => exact .branch (hf.subst σ) (ih σ) (ih' σ)

theorem subst_equivE (p : Agent V) (σ τ : V → Term W)
    (h : ∀ v, EqE (σ v) (τ v)) : EquivE (p.subst σ) (p.subst τ) := by
  induction p generalizing W with
  | nil => exact .nil
  | par p q hp hq => exact .par (hp σ τ h) (hq σ τ h)
  | output c m p hp => exact .output c (m.subst_congr σ τ h) (hp σ τ h)
  | input c p hp =>
    apply EquivE.input c (hp _ _ _)
    intro v
    cases v with
    | none => exact .refl _
    | some v => exact (h v).subst _
  | branch f p q hp hq => exact .branch (f.subst_equivE σ τ h) (hp σ τ h) (hq σ τ h)

theorem EquivE.subst_congr {p q : Agent V} (h : EquivE p q) (σ τ : V → Term W)
    (he : ∀ v, EqE (σ v) (τ v)) : EquivE (p.subst σ) (q.subst τ) :=
  (h.subst σ).trans (q.subst_equivE σ τ he)

theorem EquivE.bind {p q : Agent (Option V)} (h : EquivE p q)
    {m n : Term V} (hm : EqE m n) : EquivE (p.bind m) (q.bind n) := by
  apply h.subst_congr
  intro v
  cases v with
  | none => exact hm
  | some v => exact .refl _

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
