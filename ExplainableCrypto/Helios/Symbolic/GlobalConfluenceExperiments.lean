import ExplainableCrypto.Helios.Symbolic.RewriteExperiments

namespace ExplainableCrypto.Helios.Symbolic.GlobalConfluenceExperiments
open ExplainableCrypto.Testing RewriteExperiments

def representatives (f : Binary) : Term Nat → List (Term Nat)
  | .binary g a b => if f = g then representatives f a ++ representatives f b else [.binary g a b]
  | .const c => if f = .add ∧ (c = .zero ∨ c = .one) then [] else [.const c]
  | t => [t]

def inheritanceCheck (n : Nat) : Bool :=
  let a := generatedTerm (n % 4) n
  let b := generatedTerm (n % 4) (n + 13)
  let inner := Term.binary .compose a (.binary .add b (.const .zero))
  [Binary.mul, .compose, .add].all fun f =>
    let t := Term.binary f inner (.binary f b (.const .one))
    let inherited := representatives f inner ++ representatives f (.binary f b (.const .one))
    (representatives f t == inherited) &&
    (inherited.all fun r => r.nodeCount < t.nodeCount) &&
    (representatives .add (.binary .add (.const .zero) (.const .one))).isEmpty &&
    (representatives .mul (.binary .mul (.name n) (.const .zero))).length == 2

#eval campaign "every multiplication factor strictly decreases crypto weight (negative control)"
  (∀ n : Nat, (Term.name (V := Nat) n).cryptoWeight <
    (Term.binary .mul (.name n) (.const .zero) : Term Nat).cryptoWeight) 1 true

#eval do
  for seed in [1, 7, 42] do
    campaign "simultaneous induction inherits AC representatives from children"
      (∀ n : Nat, inheritanceCheck n = true) seed
  unless (List.range 256).all inheritanceCheck do
    throw (IO.userError "global induction mechanics backstop failed")
  IO.println "global induction mechanics backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.GlobalConfluenceExperiments
