import ExplainableCrypto.Helios.Symbolic.ExpandedAdditionExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedAddMinimumExperiments
open ExplainableCrypto.Testing

/-- Dynamic programming over reachable sums; literal one is always available. -/
def coinCount (x y target : Nat) : Nat :=
  let table := (List.range (target+1)).foldl (fun table n =>
    let next := if n = 0 then 0 else [x,y].foldl (fun best c =>
      if 0 < c ∧ c ≤ n then min best (1+(table[n-c]?).getD n) else best) n
    table ++ [next]) ([] : List Nat)
  max 1 ((table[target]?).getD target)

/-- Independent enumeration of the two denomination multiplicities. -/
def countOracle (x y target : Nat) : Nat :=
  ((List.range (target+1)).flatMap (fun i => (List.range (target+1)).filterMap (fun j =>
    if i*x+j*y ≤ target then some (max 1 (i+j+(target-i*x-j*y))) else none))).foldl min (max 1 target)

def greedyMutation (_ : Nat) : Bool :=
  decide (coinCount 3 4 6 = 6/4+(6%4)/3+(6%4)%3)

def literalMutation (_ : Nat) : Bool := decide (2*2 ≤ 2*coinCount 2 3 2)
def absentZeroMutation (_ : Nat) : Bool := decide (coinCount 2 3 0 = 0)

def check (seed : Nat) : Bool :=
  let x := seed%6
  let y := (seed/6)%6
  let a := (seed/36)%13
  let b := (seed/468)%7
  decide (coinCount x y a = countOracle x y a) &&
  decide (coinCount x y (a+b) ≤ coinCount x y a+coinCount x y b) &&
  decide (coinCount x y x = 1) && decide (coinCount x y y = 1) &&
  decide (coinCount x y 0 = 1)

#eval campaign "greedy published numeral choice (negative control)" (∀ n : Nat, greedyMutation n = true) 1 true
#eval campaign "literal lower bound with cheap results (negative control)" (∀ n : Nat, literalMutation n = true) 1 true
#eval campaign "present zero is free (negative control)" (∀ n : Nat, absentZeroMutation n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "published numeral minimum costs versus independent enumeration" (∀ n : Nat, check n = true) seed
  unless (List.range 4096).all check do
    throw (IO.userError "expanded numeric minimum backstop failed")
  IO.println "expanded numeric minimum backstop: 4096 inputs, zero through five denominations, zero through twelve targets and subadditivity"

end ExplainableCrypto.Helios.Symbolic.ExpandedAddMinimumExperiments
