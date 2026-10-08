import ExplainableCrypto.Helios.Symbolic.SourceInputBinding

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

/-- Exactly the three guard forms of the historical source calculus. -/
inductive Formula (V : Type) where
  | equal : Term V → Term V → Formula V
  | unequal : Term V → Term V → Formula V
  | both : Formula V → Formula V → Formula V

namespace Formula
variable {V W U : Type}

def subst (σ : V → Term W) : Formula V → Formula W
  | .equal a b => .equal (a.subst σ) (b.subst σ)
  | .unequal a b => .unequal (a.subst σ) (b.subst σ)
  | .both a b => .both (a.subst σ) (b.subst σ)

/-- Every literal name in a public guard must satisfy the frame's policy. -/
def Public (restricted : Finset Nat) : Formula V → Prop
  | .equal a b | .unequal a b => a.Public restricted ∧ b.Public restricted
  | .both a b => a.Public restricted ∧ b.Public restricted

/-- Guards are evaluated only after every free variable has a ground value. -/
def Holds (env : V → Ground) : Formula V → Prop
  | .equal a b => EqE (a.subst env) (b.subst env)
  | .unequal a b => ¬ EqE (a.subst env) (b.subst env)
  | .both a b => a.Holds env ∧ b.Holds env

@[simp]
theorem subst_var (f : Formula V) : f.subst Term.var = f := by
  induction f <;> simp_all [subst]

@[simp]
theorem subst_subst (f : Formula V) (σ : V → Term W) (τ : W → Term U) :
    (f.subst σ).subst τ = f.subst (fun v => (σ v).subst τ) := by
  induction f <;> simp_all [subst]

theorem holds_subst (f : Formula V) (σ : V → Term W) (env : W → Ground) :
    (f.subst σ).Holds env ↔ f.Holds (fun v => (σ v).subst env) := by
  induction f <;> simp_all [subst,Holds]
end Formula

/-- Finite static-channel plain processes. Input binds None and shifts old
variables through Some. Name restriction and extended processes are separate
source-correspondence obligations; this is not the full applied-pi calculus. -/
inductive Agent : Type → Type 1 where
  | nil : Agent V
  | par : Agent V → Agent V → Agent V
  | output : Nat → Term V → Agent V → Agent V
  | input : Nat → Agent (Option V) → Agent V
  | branch : Formula V → Agent V → Agent V → Agent V

namespace Agent
variable {V W : Type}

def subst : {V W : Type} → (V → Term W) → Agent V → Agent W
  | _, _, _, .nil => .nil
  | _, _, σ, .par p q => .par (p.subst σ) (q.subst σ)
  | _, _, σ, .output c m p => .output c (m.subst σ) (p.subst σ)
  | _, _, σ, .input c p => .input c (p.subst (liftSubst σ))
  | _, _, σ, .branch f p q => .branch (f.subst σ) (p.subst σ) (q.subst σ)

def bind (p : Agent (Option V)) (m : Term V) : Agent V :=
  p.subst (inputSubst m)

/-- Direct ground reductions before structural and restriction closure.
Comm here includes receiver substitution. SourceActiveBinding derives this
rule from atomic Comm and active-variable structural rules; the full source
name-scope/labelled converse remains part of the extended-process bridge. -/
inductive CoreStep : Agent Empty → Agent Empty → Prop where
  | comm (c : Nat) (m : Ground) (p : Agent Empty) (q : Agent (Option Empty)) :
      CoreStep (.par (.output c m p) (.input c q)) (.par p (q.bind m))
  | thenBranch (f : Formula Empty) (p q : Agent Empty) (h : f.Holds Empty.elim) :
      CoreStep (.branch f p q) p
  | elseBranch (f : Formula Empty) (p q : Agent Empty) (h : ¬ f.Holds Empty.elim) :
      CoreStep (.branch f p q) q
  | parLeft {p p' : Agent Empty} (q : Agent Empty) (h : CoreStep p p') :
      CoreStep (.par p q) (.par p' q)
  | parRight (p : Agent Empty) {q q' : Agent Empty} (h : CoreStep q q') :
      CoreStep (.par p q) (.par p q')
end Agent
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
