import ExplainableCrypto.Helios.Symbolic.ExpandedSuccessfulCheckExperiments
import ExplainableCrypto.Helios.Symbolic.SuccessfulDecryptionExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedSuccessfulDecryptionExperiments
open ExplainableCrypto.Testing Historical General
private def names (n : Nat) : Names n := ⟨0,1,fun i j => 10+i.val*(n+1)+j.val⟩
def check (seed : Nat) : Bool :=
  let n := seed%5
  let left := (BitCandidate.selected (0 : Fin (n+1))).substitution
  let right := (BitCandidate.abstain n).substitution
  [false,true].all fun swap =>
    let φ := expandedFrame (names n) swap left right []
    let secret : Recipe (ExpandedHandles n) := .var (expandedPartial 0)
    let p : Recipe (ExpandedHandles n) := if seed%2=0 then .var (expandedResult 0)
      else .binary .pair (.var (expandedOld 1)) (.var (expandedPartial 0))
    let c := Term.ternary .penc (.unary .pk secret) (.name (40+seed%3)) p
    let a := if seed%2=0 then secret else .binary .partialDecrypt secret c
    let whole := Term.binary .dec a c
    let tally := (tallyRecipe (n := n) [] 0).subst (fun i => .var (expandedOld i))
    decide (p.nodeCount<whole.nodeCount) &&
      normalizeRaw (φ.eval whole) == normalizeRaw (φ.eval p) &&
      normalizeRaw (φ.eval (.binary .dec secret tally)) == normalizeRaw (φ.eval (.var (expandedResult 0)))

def onlyConstructed (_ : Nat) : Bool :=
  let t := (tallyRecipe (n := 0) [] 0).subst (fun i => .var (expandedOld (n := 0) i))
  match t with
  | .ternary .penc _ _ _ => true
  | _ => false

#eval campaign "expanded decryption omits structured E5 (negative control)" (∀ n : Nat, DecryptionProbeExperiments.omitDirect n = true) 1 true
#eval campaign "expanded decryption omits complete E6 binding (negative control)" (∀ n : Nat, DecryptionProbeExperiments.omitBinding n = true) 1 true
#eval campaign "expanded successful decryption always has constructed ciphertext (negative control)" (∀ n : Nat, onlyConstructed n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "expanded direct/public-partial decryption and actual borrowed tally" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "expanded successful decryption backstop failed")
  IO.println "expanded successful decryption backstop: 2048 inputs, one through five candidates, actual partial keys and result/pair plaintexts, public and borrowed E6, both swaps"

end ExplainableCrypto.Helios.Symbolic.ExpandedSuccessfulDecryptionExperiments
