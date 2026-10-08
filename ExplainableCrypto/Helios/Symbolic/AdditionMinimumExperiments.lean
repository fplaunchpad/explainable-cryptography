import ExplainableCrypto.Helios.Symbolic.CompositionMinimumSPOT

namespace ExplainableCrypto.Helios.Symbolic.AdditionMinimumExperiments
open ExplainableCrypto.Testing
open Historical General

private def foldTerms (xs : List (Recipe 3)) : Recipe 3 :=
  match xs with
  | [] => .const .bottom
  | a::xs => xs.foldl (fun t a => .binary .add t a) a

private def weight : Option Nat → Nat
  | none => 0
  | some n => 2 * max 1 n

private def canonical (atoms : List (Recipe 3)) (num : Option Nat) : Recipe 3 :=
  foldTerms (atoms ++ match num with
    | none => []
    | some 0 => [.const .zero]
    | some (n+1) => List.replicate (n+1) (.const .one))

def globalZero (_ : Nat) : Bool :=
  decide ((Term.binary (V := Fin 3) .add (.name 40) (.const .zero)).addSyntaxSummary =
    (Term.name (V := Fin 3) 40).addSyntaxSummary)

def saturation (_ : Nat) : Bool :=
  decide ((Term.binary (V := Fin 3) .add (.const .one) (.const .one)).addSyntaxSummary =
    (Term.const (V := Fin 3) .one).addSyntaxSummary)

def check (seed : Nat) : Bool :=
  let atoms := (List.range (seed%5)).map fun j =>
    if (seed+j)%2=0 then LocalRootSPOT.key else (.name (40+j%2) : Recipe 3)
  let ones := seed%4
  let zeros := (seed/4)%4
  let xs := atoms ++ List.replicate ones (.const .one) ++ List.replicate zeros (.const .zero)
  let xs := if xs.isEmpty then [.const .zero] else xs
  let r := foldTerms xs.reverse
  let num := r.addSyntaxSummary.numeric
  let s := canonical atoms num
  let cost := (atoms.map fun a => a.nodeCount+1).sum + weight num
  decide (r.addSyntaxSummary = s.addSyntaxSummary) &&
  (s.nodeCount+1 == cost) && decide (s.nodeCount ≤ r.nodeCount) &&
  [false,true].all (fun swap =>
    let φ := LocalRootSPOT.world swap
    let a := (φ.eval r).addSyntaxSummary
    let b := (φ.eval s).addSyntaxSummary
    decide (a.atoms.map normalizeRaw = b.atoms.map normalizeRaw) && decide (a.numeric = b.numeric))

#eval campaign "zero deleted beside arbitrary atoms (negative control)" (∀ n : Nat, globalZero n = true) 1 true
#eval campaign "one plus one saturated (negative control)" (∀ n : Nat, saturation n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "canonical addition atom bags and exact numeric costs" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "addition minimum backstop failed")
  IO.println "addition minimum backstop: 2048 inputs, absent/present zero, repeated ones and atoms, both swaps"

end ExplainableCrypto.Helios.Symbolic.AdditionMinimumExperiments
