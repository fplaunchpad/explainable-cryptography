import ExplainableCrypto.Helios.Symbolic.SourceVisibleCorrespondence

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

/-- Fresh variable insertion; all existing variables remain under Some. -/
def Agent.shift (p : Agent V) : Agent (Option V) := p.subst (fun v => .var (some v))

/-- Single free-variable substitution. The active substitution's domain is a
variable, while its right-hand side can be an arbitrary term. -/
noncomputable def replaceVar (x : V) (m : Term V) : V → Term V := by
  classical
  exact fun y => if y=x then m else .var y

/-- Variable-restriction/active-substitution fragment of the extended source
syntax. Plain Agent still has finite static channels; name restriction and
replication are not encoded by this type. -/
inductive Extended : Type → Type 1 where
  | plain : Agent V → Extended V
  | par : Extended V → Extended V → Extended V
  | newVar : Extended (Option V) → Extended V
  | active : V → Term V → Extended V

namespace Extended

def rename : {V W : Type} → (V → W) → Extended V → Extended W
  | _, _, f, .plain p => .plain (p.subst (fun v => .var (f v)))
  | _, _, f, .par a b => .par (a.rename f) (b.rename f)
  | _, _, f, .newVar a => .newVar (a.rename (Option.map f))
  | _, _, f, .active x m => .active (f x) (m.subst (fun v => .var (f v)))

/-- The source let x=M in P, with None as its fresh restricted variable. -/
def letTerm (m : Term V) (p : Agent (Option V)) : Extended V :=
  .newVar (.par (.active none (shiftTerm m)) (.plain p))

/-- Exported active variables, independent of their payloads or uses in plain
processes. Restriction removes exactly the newly bound variable from this view. -/
def Exports : {V : Type} → Extended V → V → Prop
  | _, .plain _, _ => False
  | _, .par a b, v => a.Exports v ∨ b.Exports v
  | _, .newVar a, v => a.Exports (some v)
  | _, .active x _, v => v=x

/-- Explicit Figure 3 variable/active structural rules. plainPar is just the
two syntactic presentations of parallel plain processes in extended syntax.
Freshness in New-Par is enforced by inserting Some into the outer process. -/
inductive Structural : {V : Type} → Extended V → Extended V → Prop where
  | refl (a : Extended V) : Structural a a
  | symm {a b : Extended V} : Structural a b → Structural b a
  | trans {a b c : Extended V} : Structural a b → Structural b c → Structural a c
  | parLeft {a b : Extended V} (c : Extended V) : Structural a b → Structural (.par a c) (.par b c)
  | parRight (a : Extended V) {b c : Extended V} : Structural b c → Structural (.par a b) (.par a c)
  | newVar {a b : Extended (Option V)} : Structural a b → Structural (.newVar a) (.newVar b)
  | plainPar (p q : Agent V) : Structural (.plain (.par p q)) (.par (.plain p) (.plain q))
  | zero (a : Extended V) : Structural (.par a (.plain .nil)) a
  | assoc (a b c : Extended V) : Structural (.par (.par a b) c) (.par a (.par b c))
  | comm (a b : Extended V) : Structural (.par a b) (.par b a)
  | newPar (a : Extended V) (b : Extended (Option V)) :
      Structural (.par a (.newVar b)) (.newVar (.par (a.rename some) b))
  | alias (m : Term V) : Structural (.newVar (.active none (shiftTerm m))) (.plain .nil)
  | substPlain (x : V) (m : Term V) (p : Agent V) :
      Structural (.par (.active x m) (.plain p)) (.par (.active x m) (.plain (p.subst (replaceVar x m))))
  /-- The active-active instance of Figure 3 Subst; valid definition domains are distinct. -/
  | substActive (x y : V) (m n : Term V) (hxy : x ≠ y) :
      Structural (.par (.active x m) (.active y n))
        (.par (.active x m) (.active y (n.subst (replaceVar x m))))
  | rewrite (x : V) {m m' : Term V} : EqE m m' → Structural (.active x m) (.active x m')

/-- Internal reduction generated from atomic variable communication, ground
conditionals, and the source evaluation/structural closures. There is no
primitive arbitrary-message communication constructor. -/
inductive Reduction : {V : Type} → Extended V → Extended V → Prop where
  | atomComm (c : Nat) (x : V) (p : Agent V) (q : Agent (Option V)) :
      Reduction (.plain (.par (.output c (.var x) p) (.input c q)))
        (.plain (.par p (q.bind (.var x))))
  | thenBranch (f : Formula Empty) (p q : Agent V) (hf : f.Holds Empty.elim) :
      Reduction (.plain (.branch (f.subst Empty.elim) p q)) (.plain p)
  | elseBranch (f : Formula Empty) (p q : Agent V) (hf : ¬ f.Holds Empty.elim) :
      Reduction (.plain (.branch (f.subst Empty.elim) p q)) (.plain q)
  | parLeft {a b : Extended V} (c : Extended V) : Reduction a b → Reduction (.par a c) (.par b c)
  | parRight (a : Extended V) {b c : Extended V} : Reduction b c → Reduction (.par a b) (.par a c)
  | newVar {a b : Extended (Option V)} : Reduction a b → Reduction (.newVar a) (.newVar b)
  | congr {a a' b b' : Extended V} : Structural a a' → Reduction a' b' → Structural b' b → Reduction a b
end Extended
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
