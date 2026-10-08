import ExplainableCrypto.Helios.Symbolic.ExpandedMixedExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedPaddedExperiments
open ExplainableCrypto.Testing
open ExpandedAddMinimumExperiments
private def cost (x y total _atoms atomCost : Nat) : Nat :=
  max 2 (atomCost + if total=0 then 0 else 2*coinCount x y total)
private def oracle (x y total atoms atomCost : Nat) : Nat :=
  ((List.range (total+2)).flatMap (fun i => (List.range (total+2)).flatMap (fun j =>
    [0,1].filterMap (fun z =>
      if i*x+j*y ≤ total ∧ 0 < atoms+i+j+(total-i*x-j*y)+z then
        some (atomCost+2*(i+j+(total-i*x-j*y)+z)) else none)))).foldl min (atomCost+2*(total+1))
def literal_cost_mutation (_ : Nat) : Bool := decide (4 ≤ cost 2 3 2 0 0)
def free_zero_mutation (_ : Nat) : Bool := decide (cost 2 3 0 0 0 = 0)
def greedy_mutation (_ : Nat) : Bool := decide (cost 3 4 6 1 2 = 2+2*(6/4+(6%4)/3+(6%4)%3))
def check (seed : Nat) : Bool :=
  let x := seed%6
  let y := (seed/6)%6
  let total := (seed/36)%10
  let atoms := (seed/360)%4
  let atomCost := atoms*(2+seed%3)
  decide (cost x y total atoms atomCost = oracle x y total atoms atomCost) &&
    decide (2 ≤ cost x y total atoms atomCost) &&
    decide (cost x y total atoms atomCost ≤ atomCost+2*coinCount x y total)

#eval campaign "padded positive numerals have literal-only cost (negative control)" (∀ n : Nat, literal_cost_mutation n = true) 1 true
#eval campaign "padded all-zero payload is empty (negative control)" (∀ n : Nat, free_zero_mutation n = true) 1 true
#eval campaign "padded numeric cost is greedy (negative control)" (∀ n : Nat, greedy_mutation n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "padded numeric-handle costs versus exhaustive multiplicities" (∀ n : Nat, check n = true) seed
  unless (List.range 4096).all check do
    throw (IO.userError "expanded padded numeric backstop failed")
  IO.println "expanded padded numeric backstop: 4096 inputs, zero through five denominations, zero through nine totals, zero through three atoms of costs two through four"

end ExplainableCrypto.Helios.Symbolic.ExpandedPaddedExperiments
