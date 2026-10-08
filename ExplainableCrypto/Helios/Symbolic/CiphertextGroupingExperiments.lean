import ExplainableCrypto.Helios.Symbolic.CiphertextGrouping
import ExplainableCrypto.Helios.Symbolic.CiphertextCombinationExperiments

namespace ExplainableCrypto.Helios.Symbolic.CiphertextGroupingExperiments
open ExplainableCrypto.Testing Historical General

private def generated : Nat → Nat → CiphertextAssembly 1
  | 0, seed => if seed % 2 = 0 then .constructed (.var 0) (.name (40 + seed % 5)) (.name (80 + seed % 7))
      else .honest (⟨seed % 2, Nat.mod_lt _ (by decide)⟩, ⟨seed / 2 % 2, Nat.mod_lt _ (by decide)⟩)
  | d + 1, seed => match seed % 3 with
    | 0 => generated 0 (2 * seed)
    | 1 => generated 0 (2 * seed + 1)
    | _ => .mul (generated d (seed / 3)) (generated d (seed / 3 + 1))

private def leafLists : CiphertextAssembly 1 → List (Recipe 3) × List (Recipe 3) × List (HonestIndex 1)
  | .constructed _ r p => ([r], [p], [])
  | .honest i => ([], [], [i])
  | .mul a b =>
    let x := leafLists a
    let y := leafLists b
    (x.1 ++ y.1, x.2.1 ++ y.2.1, x.2.2 ++ y.2.2)

private def flatten (f : Binary) : Recipe 3 → List (Recipe 3)
  | .binary g a b => if g = f then flatten f a ++ flatten f b else [.binary g a b]
  | t => [t]

private def honestLeaves : Combination (HonestIndex 1) → List (HonestIndex 1)
  | .leaf i => [i]
  | .mul a b => honestLeaves a ++ honestLeaves b

private def groupedLists : CiphertextGroup 1 → List (Recipe 3) × List (Recipe 3) × List (HonestIndex 1)
  | .constructed r p => (flatten .compose r, flatten .add p, [])
  | .honest a => ([], [], honestLeaves a)
  | .mixed r p a => (flatten .compose r, flatten .add p, honestLeaves a)

private def checkTree (t : CiphertextAssembly 1) (broken := false) : Bool :=
  let x := leafLists t
  let y := groupedLists t.group
  decide (x.1.Perm (if broken then y.1.drop 1 else y.1)) &&
    decide (x.2.1.Perm y.2.1) && decide (x.2.2.Perm y.2.2) &&
    decide (t.group.budget ≤ t.recipe.nodeCount)

def groupingCheck (seed : Nat) (broken := false) : Bool :=
  checkTree (generated 4 seed) broken

/-- The three literal shapes ensure that every one of the nine root merge
branches is exercised, including both mixed operand orders. -/
private def shape (tag : Nat) : CiphertextAssembly 1 :=
  match tag % 3 with
  | 0 => .constructed (.var 0) (.name 40) (.name 80)
  | 1 => .honest (0, 0)
  | _ => .mul (.honest (1, 1)) (.constructed (.var 0) (.name 41) (.name 81))

#eval campaign "grouping loses one public nonce factor (negative control)"
  (∀ n : Nat, groupingCheck n true = true) 1 true
#eval do
  for seed in [1, 7, 42] do
    campaign "ciphertext grouping preserves public leaves, honest multiplicity and original budget"
      (∀ n : Nat, groupingCheck n = true) seed
  unless (List.range 256).all groupingCheck do
    throw (IO.userError "ciphertext-grouping backstop failed")
  unless (List.range 9).all (fun i => checkTree (.mul (shape (i % 3)) (shape (i / 3)))) do
    throw (IO.userError "ciphertext-grouping directed merge cases failed")
  IO.println "ciphertext-grouping backstop: 256 inputs and all nine directed merge cases passed"

end ExplainableCrypto.Helios.Symbolic.CiphertextGroupingExperiments
