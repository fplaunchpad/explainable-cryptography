import Plausible

namespace ExplainableCrypto.Testing

open Plausible Plausible.Decorations in
def campaign (label : String) (p : Prop)
    (seed : Nat) (expectFailure : Bool := false)
    (p' : DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit := do
  let result ← Testable.checkIO p'
    { numInst := 500, maxSize := 40, randomSeed := some seed }
  match result with
  | .success _ =>
    if expectFailure then throw (IO.userError s!"{label}: missed known defect")
    IO.println s!"{label}: seed={seed}; configured cases=500; size=40; success; gaveUp=0"
  | .gaveUp n => throw (IO.userError s!"{label}: gaveUp {n}")
  | .failure _ values shrinks =>
    if !expectFailure then
      throw (IO.userError s!"{label}: unexpected failure {values}; shrinks={shrinks}")
    IO.println s!"{label}: seed={seed}; expected counterexample={values}; shrinks={shrinks}"

end ExplainableCrypto.Testing
