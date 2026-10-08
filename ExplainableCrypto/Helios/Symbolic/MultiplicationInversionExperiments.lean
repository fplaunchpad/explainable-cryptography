import ExplainableCrypto.Helios.Symbolic.DecryptionPathExperiments

namespace ExplainableCrypto.Helios.Symbolic.MultiplicationInversionExperiments
open ExplainableCrypto.Testing DecryptionPathExperiments

/-- Raw product, independently assembled nonce tree and message tree. -/
def tree : Nat → Nat → Term Nat × Term Nat × Term Nat
  | 0, seed =>
    let r : Term Nat := .name (10 + seed)
    let m : Term Nat := .name (40 + seed)
    (reveal (enc (.name 0) r (reveal m)), r, m)
  | depth + 1, seed =>
    let (a, r, m) := tree depth (seed / 2)
    let (b, s, n) := tree depth (seed / 3 + 7)
    (reveal (.binary .mul a b), .binary .compose r s, .binary .add m n)

def inversionCheck (seed : Nat) : Bool :=
  let (a, r, m) := tree (seed % 3) seed
  let (b, s, n) := tree ((seed + 1) % 3) (seed + 19)
  (normalizeRaw a == enc (.name 0) r m) &&
    (normalizeRaw b == enc (.name 0) s n) &&
    (normalizeRaw (.binary .mul a b) == enc (.name 0) (.binary .compose r s) (.binary .add m n))

#eval campaign "different named keys still fuse (negative control)"
  (∀ n : Nat,
    (match normalizeRaw (.binary .mul
      (enc (.name 0) (.name 10) (.name n))
      (enc (.name 1) (.name 11) (.name n))) with
      | .ternary .penc _ _ _ => true | _ => false) = true) 1 true

#eval do
  for seed in [1, 7, 42] do
    campaign "ciphertext operand values and combined components through expanding factors"
      (∀ n : Nat, inversionCheck n = true) seed
  unless (List.range 256).all inversionCheck do
    throw (IO.userError "multiplication inversion backstop failed")
  IO.println "multiplication inversion backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.MultiplicationInversionExperiments
