import ExplainableCrypto.Helios.Symbolic.BaseStructure
import ExplainableCrypto.Helios.Symbolic.RewriteExperiments

namespace ExplainableCrypto.Helios.Symbolic.BaseStructureExperiments
open ExplainableCrypto.Testing RewriteExperiments

/-- A deliberately wrong observation that treats every addition as a binary root. -/
def rawIsAdd : Term Nat → Bool
  | .binary .add _ _ => true
  | _ => false

#eval campaign "raw outer constructor is E0-invariant (negative control)"
  (∀ n : Nat, rawIsAdd (.binary .add (.const .zero) (.const .one)) =
    rawIsAdd (.const .one) ∧ n = n) 1 true

def structureCheck (n : Nat) : Bool :=
  let a := generatedTerm (n % 4) n
  let b := generatedTerm (n % 4) (n + 13)
  let c := generatedTerm (n % 4) (n + 29)
  (backgroundPairs a b c).all (fun (l, r) =>
    l.headTag == r.headTag &&
    (wrap (n % 4) a l).headTag == (wrap (n % 4) a r).headTag) &&
  ((Term.name n : Term Nat).headTag != (Term.name (n + 1) : Term Nat).headTag) &&
  ((Term.ternary .penc a b c).headTag != (Term.spk a b c a).headTag) &&
  ((Term.ternary .penc a b c).rigidArgument 1 == b) &&
  ((Term.binary .mul a b).rigidArgument 0 == .const .bottom)

#eval do
  for seed in [1, 7, 42] do
    campaign "E0 head observations and rigid argument fixtures"
      (∀ n : Nat, structureCheck n = true) seed
  unless (List.range 256).all structureCheck do
    throw (IO.userError "background-structure deterministic backstop failed")
  IO.println "background-structure deterministic backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.BaseStructureExperiments
