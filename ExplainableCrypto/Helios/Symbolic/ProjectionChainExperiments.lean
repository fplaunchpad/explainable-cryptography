import ExplainableCrypto.Helios.Symbolic.RewriteExperiments
import ExplainableCrypto.Helios.Symbolic.RawNormalization
import ExplainableCrypto.Helios.Symbolic.TupleGuard

namespace ExplainableCrypto.Helios.Symbolic.ProjectionChainExperiments
open ExplainableCrypto.Testing RewriteExperiments

/-- Words are applied from innermost to outermost; true selects fst. -/
def select (t : Term Nat) (word : List Bool) : Term Nat :=
  word.foldl (fun a first => .unary (if first then .fst else .snd) a) t
def isPair (t : Term Nat) : Bool := match t with | .binary .pair _ _ => true | _ => false
def isCipher (t : Term Nat) : Bool := match t with | .ternary .penc _ _ _ => true | _ => false

def chainCheck (seed : Nat) : Bool :=
  let k := generatedTerm (seed % 4) seed
  let r := generatedTerm (seed % 4) (seed + 13)
  let count := 1 + seed % 4
  let ciphers := (List.range count).map (fun i => Term.ternary .penc k r (.name i))
  let proofs := (List.range count).map (fun i => Term.spk k r (.name i) (.const .bottom))
  let fields := ciphers ++ proofs
  let words := (List.range 10).flatMap (fun n =>
    [List.replicate n false, List.replicate n false ++ [true],
     List.replicate n false ++ [true, false],
     (List.range n).map (fun j => (seed / (2 ^ j)) % 2 == 1)])
  words.all (fun word =>
    let out := normalizeRaw (select (Term.tuple fields) word)
    (!isPair out || (word.all (! ·) && word.length < fields.length)) &&
    (!isCipher out || ((List.range count).any
      (fun i => word == List.replicate i false ++ [true] &&
        out == normalizeRaw (.ternary .penc k r (.name i))))))

#eval campaign "pure-tail classification without the non-pair-field premise (negative control)"
  (∀ n : Nat, isPair (normalizeRaw (select
    (Term.tuple [.binary .pair (.name n) (.name 1)]) [true])) = false) 1 true

#eval do
  for seed in [1, 7, 42] do
    campaign "projection-chain pair and ciphertext origins"
      (∀ n : Nat, chainCheck n = true) seed
  unless (List.range 256).all chainCheck do
    throw (IO.userError "projection-chain backstop failed")
  IO.println "projection-chain backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.ProjectionChainExperiments
