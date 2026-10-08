import ExplainableCrypto.Helios.Symbolic.AddSummary
import ExplainableCrypto.Testing.Plausible

namespace ExplainableCrypto.Helios.Symbolic.AddSummaryExperiments
open ExplainableCrypto.Testing

#eval campaign "zero is an identity for arbitrary summands (negative control)"
  (∀ n : Nat, AddSummary.combine (AddSummary.atom n) (AddSummary.number 0) = AddSummary.atom n) 1 true

#eval campaign "positive numeric sums saturate to one (negative control)"
  (∀ n : Nat, AddSummary.combine (AddSummary.number (n + 1) : AddSummary Nat)
    (AddSummary.number 1) = AddSummary.number 1) 1 true

def generated (n : Nat) : AddSummary Nat :=
  ⟨((List.range (n % 6)).map (fun i => (n / (i + 1) + i) % 4) : Multiset Nat),
    if n % 3 = 0 then none else some (n % 4)⟩

def token (n : Nat) : AddSummary Nat :=
  if n = 0 then .number 0 else if n = 1 then .number 1 else .atom (n - 2)

def summaryCheck (n : Nat) : Bool :=
  let a := generated n
  let b := generated (n + 7)
  let c := generated (n + 17)
  let xs := (List.range (1 + n % 9)).map (fun i => (n / (i + 1) + i) % 6)
  let folded := xs.foldl (fun (s : AddSummary Nat) x => s.combine (token x)) AddSummary.empty
  let expectedAtoms : Multiset Nat := (xs.filter (fun x => 2 ≤ x)).map (fun x => x - 2)
  let expectedNumeric := if xs.any (fun x => x ≤ 1) then some ((xs.filter (· == 1)).length) else none
  decide (a.combine b = b.combine a ∧
    (a.combine b).combine c = a.combine (b.combine c) ∧
    a.combine .empty = a ∧ AddSummary.empty.combine a = a ∧
    folded.atoms = expectedAtoms ∧ folded.numeric = expectedNumeric)

#eval do
  for seed in [1, 7, 42] do
    campaign "addition summaries preserve numeric presence and exact flat-token counts"
      (∀ n : Nat, summaryCheck n = true) seed
  unless (List.range 256).all summaryCheck do
    throw (IO.userError "addition-summary deterministic backstop failed")
  IO.println "addition-summary deterministic backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.AddSummaryExperiments
