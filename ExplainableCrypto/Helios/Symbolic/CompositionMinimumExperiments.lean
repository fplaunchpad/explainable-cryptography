import ExplainableCrypto.Helios.Symbolic.ConstructedCiphertextSPOT

namespace ExplainableCrypto.Helios.Symbolic.CompositionMinimumExperiments
open ExplainableCrypto.Testing
open Historical General

def zeroUnit (_ : Nat) : Bool :=
  let t : Recipe 3 := .binary .compose (.name 40) (.const .zero)
  decide (t.composeLeaves = (Term.name (V := Fin 3) 40).composeLeaves)

def idempotent (_ : Nat) : Bool :=
  let t : Recipe 3 := .binary .compose (.name 40) (.name 40)
  decide (t.composeLeaves = (Term.name (V := Fin 3) 40).composeLeaves)

private def leaf (k : Nat) : Recipe 3 :=
  match k % 6 with
  | 0 => .name 40
  | 1 => .var 0
  | 2 => .const .zero
  | 3 => LocalRootSPOT.key
  | 4 => .unary .fst (.var 0)
  | _ => .ternary .penc (.var 0) (.name 40) (.const .one)

private def tree (xs : List (Recipe 3)) : Recipe 3 :=
  match xs with
  | [] => .const .bottom
  | x::xs => xs.foldl (fun t a => .binary .compose t a) x

def check (seed : Nat) : Bool :=
  let xs := (List.range (seed%7+1)).map fun j => leaf (seed+j*j)
  let a := tree xs
  let b := tree xs.reverse
  decide ((a.composeLeaves.map Term.nodeCount).sum + a.composeLeaves.card = a.nodeCount+1) &&
  decide ((b.composeLeaves.map Term.nodeCount).sum + b.composeLeaves.card = b.nodeCount+1) &&
  decide (a.composeLeaves = b.composeLeaves) && (a.nodeCount == b.nodeCount) &&
  [false,true].all (fun swap =>
    let φ := LocalRootSPOT.world swap
    decide ((φ.eval a).composeLeaves.map normalizeRaw = (φ.eval b).composeLeaves.map normalizeRaw))

#eval campaign "zero used as composition identity (negative control)" (∀ n : Nat, zeroUnit n = true) 1 true
#eval campaign "composition occurrences collapsed (negative control)" (∀ n : Nat, idempotent n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "composition leaf costs and occurrence-preserving permutations" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "composition minimum backstop failed")
  IO.println "composition minimum backstop: 2048 inputs, one through seven leaves, both swaps"

end ExplainableCrypto.Helios.Symbolic.CompositionMinimumExperiments
