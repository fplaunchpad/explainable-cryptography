import ExplainableCrypto.Helios.Symbolic.AdditionObservationExperiments

namespace ExplainableCrypto.Helios.Symbolic.MultiplicationObservationExperiments
open ExplainableCrypto.Testing
private def cipher (key nonce bit : Nat) : Ground :=
  .ternary .penc (.name key) (.name nonce) (if bit % 2 = 0 then .const .zero else .const .one)
private def leaves : Ground → List Ground
  | .binary .mul a b => leaves a ++ leaves b
  | t => [t]
private def reveal (t : Ground) := Term.unary .fst (.binary .pair t (.const .bottom))

/-- The whole output is still a product, but two ciphertext occurrences fuse. -/
def unfusedBag (_seed : Nat) : Bool :=
  let a := cipher 40 41 0
  let b := cipher 40 42 1
  let t := Term.binary .mul (.binary .mul a b) (.name 50)
  decide ((leaves t).length = (leaves (normalizeRaw t)).length)

def hiddenProduct (_seed : Nat) : Bool :=
  let t := reveal (.binary .mul (.name 40) (.name 41))
  decide ((leaves t).length = (leaves (normalizeRaw t)).length)

private def piece : List Ground → Ground
  | [] => .const .bottom
  | a :: xs => xs.foldl (Term.binary .mul) a

/-- Labels partition original occurrences, not just their values. A raw recipe
with k leaves has size+1 equal to the sum of each leaf's size+1. -/
def partitionCheck (seed : Nat) : Bool :=
  let count := 2 + seed % 7
  let xs := (List.range count).map (fun i => cipher (40 + (seed / (i+1)) % 3) (50 + i % 3) (seed+i))
  let source := Term.binary .mul (piece xs) (.name 60)
  let groups := (List.range 3).map (fun k => xs.filter (fun t => match t with
    | .ternary .penc (.name key) _ _ => key == 40+k | _ => false))
  let groups := groups.filter (fun g => !g.isEmpty)
  let pieces := (groups.map piece) ++ [.name 60]
  let a := cipher 40 (50 + seed % 3) seed
  let b := cipher 40 (50 + seed / 3 % 3) (seed+1)
  let fused := normalizeRaw (.binary .mul a b)
  let expected := Term.ternary .penc (.name 40)
    (.binary .compose (.name (50 + seed % 3)) (.name (50 + seed / 3 % 3)))
    (.binary .add (if seed % 2 = 0 then .const .zero else .const .one)
      (if (seed+1) % 2 = 0 then .const .zero else .const .one))
  decide (groups.flatten.Perm xs) && decide (fused = expected) &&
    decide ((pieces.map (fun t => t.nodeCount+1)).sum = source.nodeCount+1) &&
    pieces.all (fun t => t.nodeCount < source.nodeCount) &&
    decide ((leaves (normalizeRaw (.binary .mul (.binary .mul a b) (.name 60)))).length = 2)

#eval campaign "unfused multiplication bag (negative control)" (∀ n : Nat, unfusedBag n = true) 1 true
#eval campaign "hidden multiplication atom (negative control)" (∀ n : Nat, hiddenProduct n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "multiplication fusion partitions retain occurrences and strict group budgets" (∀ n : Nat, partitionCheck n = true) seed
  unless (List.range 2048).all partitionCheck do
    throw (IO.userError "multiplication partition backstop failed")
  IO.println "multiplication partition backstop: 2048 inputs passed"

end ExplainableCrypto.Helios.Symbolic.MultiplicationObservationExperiments
