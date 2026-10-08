import ExplainableCrypto.Helios.Symbolic.ConstructedCompressionSPOT

namespace ExplainableCrypto.Helios.Symbolic.JointMinimumExperiments
open ExplainableCrypto.Testing MinimumTransportExperiments

def below (size source target : Fin 4 → Nat) (bound : Nat) : Bool :=
  (List.finRange 4).all fun r => size r ≥ bound ||
    (List.finRange 4).any fun m => minimum size source m &&
      source r == source m && target r == target m

def observations (size source target : Fin 4 → Nat) (bound : Nat) : Bool :=
  (List.finRange 4).all fun r => (List.finRange 4).all fun s =>
    size r + size s ≥ bound || agrees source target r s

def bothStep (size source target : Fin 4 → Nat) : Bool :=
  (List.finRange 4).all fun r => (List.finRange 4).all fun s =>
    !(minimum size source r && minimum size source s &&
      minimum size target r && minimum size target s) ||
    !observations size source target (size r + size s) || agrees source target r s

def positive (size source target : Fin 4 → Nat) (bound : Nat) : Bool :=
  below size source target bound && below size target source bound && bothStep size source target

def check (seed : Nat) : Bool :=
  let size := fun i : Fin 4 => 1 + (seed / 2^i.val) % 2
  let source := fun i : Fin 4 => (seed / 2^(4+i.val)) % 2
  let target := fun i : Fin 4 => (seed / 2^(8+i.val)) % 2
  [0,1,2,3,4,5].all fun bound =>
    !positive size source target bound || observations size source target bound

def costs : Fin 4 → Nat := fun i => if i = 1 then 2 else 1
def distinct : Fin 4 → Nat := fun i => i.val
def merged : Fin 4 → Nat := fun i => if i = 1 then 0 else i.val

def missingReverse (_ : Nat) : Bool :=
  !(below costs distinct merged 4 && bothStep costs distinct merged) ||
    observations costs distinct merged 4
def missingStep (_ : Nat) : Bool :=
  let size : Fin 4 → Nat := fun _ => 1
  !(below size distinct merged 3 && below size merged distinct 3) ||
    observations size distinct merged 3
def insufficientBound (_ : Nat) : Bool :=
  !positive costs distinct merged 2 || observations costs distinct merged 4

#eval campaign "bounded transport without reverse minima (negative control)" (∀ n : Nat, missingReverse n = true) 1 true
#eval campaign "bounded transport without minimum observation step (negative control)" (∀ n : Nat, missingStep n = true) 1 true
#eval campaign "two-way minima supplied at an insufficient bound (negative control)" (∀ n : Nat, insufficientBound n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "two-way bounded shared minima lift bounded observations" (∀ n : Nat, check n = true) seed
  unless (List.range 4096).all check do
    throw (IO.userError "joint minimum exhaustive backstop failed")
  let hits := (List.range 4096).foldl (fun total seed =>
    let size := fun i : Fin 4 => 1 + (seed / 2^i.val) % 2
    let source := fun i : Fin 4 => (seed / 2^(4+i.val)) % 2
    let target := fun i : Fin 4 => (seed / 2^(8+i.val)) % 2
    total + ([0,1,2,3,4,5].filter (positive size source target)).length) 0
  IO.println s!"joint minimum backstop: all 4096 models at six bounds; {hits} premise-satisfying instances"

end ExplainableCrypto.Helios.Symbolic.JointMinimumExperiments
