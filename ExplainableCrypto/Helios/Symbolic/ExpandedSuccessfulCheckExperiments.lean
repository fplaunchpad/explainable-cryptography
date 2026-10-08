import ExplainableCrypto.Helios.Symbolic.ExpandedPairMinimumExperiments
import ExplainableCrypto.Helios.Symbolic.SuccessfulCheckExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedSuccessfulCheckExperiments
open ExplainableCrypto.Testing Historical General
private def cipherView : Ground → Option (Ground × Multiset Ground × AddSummary Ground)
  | .ternary .penc k r m => some (k,r.composeLeaves,m.addSyntaxSummary)
  | _ => none
private def valid (key cipher proof : Ground) : Bool :=
  match normalizeRaw proof with
  | .spk k r m d =>
    let ms := m.addSyntaxSummary
    decide (normalizeRaw key=k) && decide (ms.atoms=0) &&
      (ms.numeric == some 0 || ms.numeric == some 1) &&
      decide (cipherView (normalizeRaw cipher)=some (k,r.composeLeaves,ms)) &&
      decide (cipherView d=cipherView (normalizeRaw cipher))
  | _ => false

private def names (n : Nat) : Names n := ⟨0,1,fun i j => 10+i.val*(n+1)+j.val⟩
def check (seed : Nat) : Bool :=
  let n := seed%5
  let left := (BitCandidate.selected (0 : Fin (n+1))).substitution
  let right := (BitCandidate.abstain n).substitution
  [false,true].all fun swap =>
    let φ := expandedFrame (names n) swap left right []
    let k : Recipe (ExpandedHandles n) := .unary .pk (.var (expandedPartial 0))
    let r : Recipe (ExpandedHandles n) := .var (expandedPartial 0)
    let m : Recipe (ExpandedHandles n) := if seed%2=0 then .var (expandedResult 0) else .const .zero
    let c := Term.ternary .penc k r m
    valid (φ.eval k) (φ.eval c) (φ.eval (.spk k r m c)) &&
      [0,1].all fun i : Fin 2 =>
        let v := (choice swap left right i).value
        (List.finRange (n+1)).all (fun j => valid (publicKey (names n))
          (ciphertext (names n) i v j) (componentProof (names n) i v j)) &&
        valid (publicKey (names n)) (foldCandidates .mul (ciphertext (names n) i v))
          (aggregateProof (names n) i v)

#eval campaign "expanded check ignores ciphertext binding (negative control)" (∀ n : Nat, SuccessfulCheckExperiments.wrongBinding n = true) 1 true
#eval campaign "expanded check ignores supplied key (negative control)" (∀ n : Nat, SuccessfulCheckExperiments.wrongKey n = true) 1 true
#eval campaign "expanded check accepts non-bit (negative control)" (∀ n : Nat, SuccessfulCheckExperiments.nonBit n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "expanded successful checks with actual published inputs and honest proofs" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "expanded successful check backstop failed")
  IO.println "expanded successful check backstop: 2048 inputs, one through five candidates, actual partial/result inputs, honest components/aggregates, both swaps"

end ExplainableCrypto.Helios.Symbolic.ExpandedSuccessfulCheckExperiments
