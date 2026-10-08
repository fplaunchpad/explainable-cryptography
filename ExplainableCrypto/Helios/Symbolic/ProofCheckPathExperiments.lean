import ExplainableCrypto.Helios.Symbolic.RewriteExperiments
import ExplainableCrypto.Helios.Symbolic.RawNormalization

namespace ExplainableCrypto.Helios.Symbolic.ProofCheckPathExperiments
open ExplainableCrypto.Testing RewriteExperiments

def reveal (t : Term Nat) : Term Nat := .unary .fst (.binary .pair t (.const .bottom))
def cipher (k r : Term Nat) (bit : Constant) : Term Nat := .ternary .penc k r (.const bit)
def proof (k r : Term Nat) (bit : Constant) : Term Nat := .spk k r (.const bit) (cipher k r bit)
def delayed (k r : Term Nat) (bit : Constant) : Term Nat :=
  .ternary .checkspk (reveal k) (reveal (cipher k r bit)) (reveal (proof k r bit))
def retained (t : Term Nat) : Bool :=
  match t with | .ternary .checkspk _ _ _ => true | _ => false

def pathCheck (seed : Nat) : Bool :=
  let k := generatedTerm (seed % 4) seed
  let r := generatedTerm (seed % 4) (seed + 13)
  let p := generatedTerm (seed % 4) (seed + 23)
  let out := normalizeRaw (.ternary .checkspk k r p)
  (normalizeRaw (delayed k r .zero) == .const .ok) &&
  (normalizeRaw (delayed k r .one) == .const .ok) &&
  retained (normalizeRaw (delayed k r .bottom)) &&
  retained (normalizeRaw (delayed k r .ok)) &&
  retained (normalizeRaw (.ternary .checkspk (reveal k) (reveal (cipher k r .zero))
    (reveal (.spk k r (.const .zero) (cipher k r .one))))) &&
  (retained out || out == .const .ok)

#eval campaign "successful checking retains its literal head (negative control)"
  (∀ n : Nat, retained (normalizeRaw (delayed (.name n) (.name 1) .zero)) = true) 1 true

#eval do
  for seed in [1, 7, 42] do
    campaign "delayed E8/E9 paths and checking output heads"
      (∀ n : Nat, pathCheck n = true) seed
  unless (List.range 256).all pathCheck do
    throw (IO.userError "proof-check path backstop failed")
  IO.println "proof-check path backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.ProofCheckPathExperiments
