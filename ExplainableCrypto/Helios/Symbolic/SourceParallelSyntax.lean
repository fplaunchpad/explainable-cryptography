import ExplainableCrypto.Helios.Symbolic.SourceElectionReduction

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
variable {V : Type}

/-- The source parallel structural laws, closed by parallel evaluation contexts.
There is no rewriting below an input, output or conditional prefix. -/
inductive ParEq : Agent V → Agent V → Prop where
  | refl (p) : ParEq p p
  | symm {p q} : ParEq p q → ParEq q p
  | trans {p q r} : ParEq p q → ParEq q r → ParEq p r
  | zero (p) : ParEq (.par p .nil) p
  | assoc (p q r) : ParEq (.par (.par p q) r) (.par p (.par q r))
  | comm (p q) : ParEq (.par p q) (.par q p)
  | par {p p' q q'} : ParEq p p' → ParEq q q' → ParEq (.par p q) (.par p' q')

/-- Only active parallel structure is flattened; prefixes remain whole syntax. -/
def threadList : Agent V → List (Agent V)
  | .nil => []
  | .par p q => threadList p ++ threadList q
  | p => [p]

def threads (p : Agent V) : Multiset (Agent V) := p.threadList

def parallelList : List (Agent V) → Agent V
  | [] => .nil
  | p :: ps => .par p (parallelList ps)

/-- Internal reduction closed on both sides by these parallel laws. The full
source restriction/extended-process closure is a later layer. -/
def Tau (p q : Agent Empty) : Prop :=
  ∃ p' q', ParEq p p' ∧ CoreStep p' q' ∧ ParEq q' q

/-- Primitive source core reductions, with no parallel context constructors. -/
inductive PrimitiveStep : Agent Empty → Agent Empty → Prop where
  | comm (c : Nat) (m : Ground) (p : Agent Empty) (q : Agent (Option Empty)) :
      PrimitiveStep (.par (.output c m p) (.input c q)) (.par p (q.bind m))
  | thenBranch (f : Formula Empty) (p q : Agent Empty) (h : f.Holds Empty.elim) :
      PrimitiveStep (.branch f p q) p
  | elseBranch (f : Formula Empty) (p q : Agent Empty) (h : ¬ f.Holds Empty.elim) :
      PrimitiveStep (.branch f p q) q

/-- A single primitive redex and an unchanged parallel context, presented by
multisets. Contexts are actual processes, so no unrealizable thread bag is used. -/
def ThreadReduction (before after : Multiset (Agent Empty)) : Prop :=
  ∃ p q context : Agent Empty, PrimitiveStep p q ∧
    before = p.threads + context.threads ∧ after = q.threads + context.threads
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
