import ExplainableCrypto.Helios.Symbolic.PaddedMinimumSPOT

namespace ExplainableCrypto.Helios.Symbolic.SuccessfulCheckExperiments
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
private def wrap (t : Recipe 3) : Recipe 3 := .unary .fst (.binary .pair t (.const .bottom))

def wrongBinding (_ : Nat) : Bool :=
  valid (.name 40) (.ternary .penc (.name 40) (.name 41) (.const .zero))
    (.spk (.name 40) (.name 41) (.const .zero) (.ternary .penc (.name 40) (.name 42) (.const .zero)))
def wrongKey (_ : Nat) : Bool :=
  valid (.name 42) (.ternary .penc (.name 40) (.name 41) (.const .one))
    (.spk (.name 40) (.name 41) (.const .one) (.ternary .penc (.name 40) (.name 41) (.const .one)))
def nonBit (_ : Nat) : Bool :=
  let m : Ground := .binary .add (.const .one) (.const .one)
  valid (.name 40) (.ternary .penc (.name 40) (.name 41) m)
    (.spk (.name 40) (.name 41) m (.ternary .penc (.name 40) (.name 41) m))

def check (seed : Nat) : Bool :=
  let k : Recipe 3 := if seed%2=0 then .var 0 else LocalRootSPOT.key
  let r : Recipe 3 := .name (40+seed%3)
  let m : Recipe 3 := if seed%2=0 then .const .zero else .const .one
  let c := Term.ternary .penc k r m
  let proof := Term.spk (wrap k) r (wrap m) (wrap c)
  let a := wrap k
  let b := wrap c
  let bound := (Term.ternary .checkspk a b proof).nodeCount
  decide (a.nodeCount+(wrap k).nodeCount<bound) &&
    decide (b.nodeCount+(wrap c).nodeCount<bound) &&
    decide ((wrap m).nodeCount+1<bound) &&
    decide ((wrap c).nodeCount+(Term.ternary .penc (wrap k) r (wrap m)).nodeCount=proof.nodeCount) &&
    decide (proof.nodeCount<bound) &&
    [false,true].all (fun swap =>
      let φ := LocalRootSPOT.world swap
      valid (φ.eval a) (φ.eval b) (φ.eval proof) &&
      [0,1].all (fun i : Fin 2 =>
        let v := (choice swap LocalRootSPOT.left LocalRootSPOT.right i).value
        [0,1].all (fun j : Fin 2 => valid (publicKey LocalRootSPOT.names)
          (ciphertext LocalRootSPOT.names i v j) (componentProof LocalRootSPOT.names i v j)) &&
        valid (publicKey LocalRootSPOT.names) (foldCandidates .mul (ciphertext LocalRootSPOT.names i v))
          (aggregateProof LocalRootSPOT.names i v)))

#eval campaign "successful check ignores bound ciphertext (negative control)" (∀ n : Nat, wrongBinding n = true) 1 true
#eval campaign "successful check ignores key (negative control)" (∀ n : Nat, wrongKey n = true) 1 true
#eval campaign "successful check accepts two ones (negative control)" (∀ n : Nat, nonBit n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "successful proof checks retain bindings and strict observation budgets" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "successful check backstop failed")
  IO.println "successful check backstop: 2048 inputs, public constructors, honest components/aggregates and both swaps"

end ExplainableCrypto.Helios.Symbolic.SuccessfulCheckExperiments
