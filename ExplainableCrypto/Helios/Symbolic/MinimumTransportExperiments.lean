import ExplainableCrypto.Helios.Symbolic.MultiplicationObservationExperiments

namespace ExplainableCrypto.Helios.Symbolic.MinimumTransportExperiments
open ExplainableCrypto.Testing

/-- A finite inference check, independent of the cryptographic term algebra. -/
def minimum (size value : Fin 4 → Nat) (r : Fin 4) : Bool :=
  (List.finRange 4).all fun s => value r != value s || size r ≤ size s

def agrees (source target : Fin 4 → Nat) (r s : Fin 4) : Bool :=
  decide ((source r = source s) ↔ (target r = target s))

def shared (size source target : Fin 4 → Nat) : Bool :=
  (List.finRange 4).all fun r => (List.finRange 4).any fun m =>
    minimum size source m && source r == source m && target r == target m

def allTests (source target : Fin 4 → Nat) : Bool :=
  (List.finRange 4).all fun r => (List.finRange 4).all fun s => agrees source target r s

/-- The actual induction premise: all smaller tests imply this minimum test. -/
def step (size source target : Fin 4 → Nat) : Bool :=
  (List.finRange 4).all fun r => (List.finRange 4).all fun s =>
    !(minimum size source r && minimum size source s) ||
    !((List.finRange 4).all fun a => (List.finRange 4).all fun b =>
      !(size a + size b < size r + size s) || agrees source target a b) ||
    agrees source target r s

def fixtureSize : Fin 4 → Nat := fun i => if i = 2 then 2 else 1
def fixtureSource : Fin 4 → Nat := fun i => if i = 3 then 2 else if i = 1 then 1 else 0
def fixtureTarget : Fin 4 → Nat := fun i => if i = 3 then 2 else if i = 0 then 0 else 1

def missingTransport (_ : Nat) : Bool :=
  !step fixtureSize fixtureSource fixtureTarget || allTests fixtureSource fixtureTarget

/-- Exhaustively encodable positive sizes and independently chosen value maps. -/
def check (seed : Nat) : Bool :=
  let size := fun i : Fin 4 => 1 + (seed / 2^i.val) % 2
  let source := fun i : Fin 4 => (seed / 2^(4+i.val)) % 2
  let target := fun i : Fin 4 => (seed / 2^(8+i.val)) % 2
  !(shared size source target && step size source target) || allTests source target

/-- The child shrinks to a three-node pair, but its comparison exceeds the
parent/name observation budget: 6+3 is greater than 7+1. -/
def childBudget (_ : Nat) : Bool :=
  let child : Ground := .binary .pair
    (.unary .fst (.binary .pair (.name 40) (.const .bottom))) (.name 41)
  let minimum : Ground := .binary .pair (.name 40) (.name 41)
  let parent : Ground := .unary .fst child
  decide (child.nodeCount + minimum.nodeCount < parent.nodeCount + 1)

#eval campaign "child minimization within total observation budget (negative control)"
  (∀ n : Nat, childBudget n = true) 1 true
#eval campaign "minimum-pair step without shared transport (negative control)"
  (∀ n : Nat, missingTransport n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "shared minima and the smaller-test step lift all observations"
      (∀ n : Nat, check n = true) seed
  unless (List.range 4096).all check do
    throw (IO.userError "minimum transport exhaustive backstop failed")
  IO.println "minimum transport backstop: all 4096 binary-value/positive-size models passed"

end ExplainableCrypto.Helios.Symbolic.MinimumTransportExperiments
