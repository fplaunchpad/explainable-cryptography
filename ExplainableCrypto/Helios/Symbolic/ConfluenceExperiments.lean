import ExplainableCrypto.Helios.Symbolic.RewriteExperiments

namespace ExplainableCrypto.Helios.Symbolic.ConfluenceExperiments
open ExplainableCrypto.Testing RewriteExperiments

abbrev enc (k r m : Term Nat) := Term.ternary .penc k r m

def combineLeft (k r s t m n p : Term Nat) : Option (Term Nat) := do
  let ab ← (rootReduce (.binary .mul (enc k r m) (enc k s n))).map Subtype.val
  (rootReduce (.binary .mul ab (enc k t p))).map Subtype.val

def combineRight (k r s t m n p : Term Nat) : Option (Term Nat) := do
  let bc ← (rootReduce (.binary .mul (enc k s n) (enc k t p))).map Subtype.val
  (rootReduce (.binary .mul (enc k r m) bc)).map Subtype.val

/-- Only the one known associativity alignment for this directed overlap.
This is not a general E0 normaliser or equality decision procedure. -/
def alignTriple : Term Nat → Term Nat
  | .ternary .penc k (.binary .compose (.binary .compose r s) t)
      (.binary .add (.binary .add m n) p) =>
    .ternary .penc k (.binary .compose r (.binary .compose s t))
      (.binary .add m (.binary .add n p))
  | x => x

#eval campaign "raw triple endpoints need not be identical (negative control)"
  (∀ n : Nat, combineLeft (.name n) (.name 1) (.name 2) (.name 3)
      (.const .zero) (.const .one) (.const .zero) =
    combineRight (.name n) (.name 1) (.name 2) (.name 3)
      (.const .zero) (.const .one) (.const .zero)) 1 true

#eval do
  for seed in [1, 7, 42] do
    campaign "triple combination joins after the specified AC alignment" (∀ n : Nat,
      let k := generatedTerm (n % 4) n
      let r := generatedTerm (n % 4) (n + 3)
      let s := generatedTerm (n % 4) (n + 7)
      let t := generatedTerm (n % 4) (n + 11)
      let m := generatedTerm (n % 4) (n + 17)
      let q := generatedTerm (n % 4) (n + 23)
      let p := generatedTerm (n % 4) (n + 31)
      (combineLeft k r s t m q p).map alignTriple = combineRight k r s t m q p ∧
      (combineRight k r s t m q p).isSome = true) seed

end ExplainableCrypto.Helios.Symbolic.ConfluenceExperiments
