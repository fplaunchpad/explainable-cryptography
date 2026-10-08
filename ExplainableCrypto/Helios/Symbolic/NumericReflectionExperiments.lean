import ExplainableCrypto.Helios.Symbolic.AddSummaryExperiments

namespace ExplainableCrypto.Helios.Symbolic.NumericReflectionExperiments
open ExplainableCrypto.Testing

private def summary (seed : Nat) : AddSummary Nat :=
  ⟨↑([seed % 3, seed / 3 % 3].take (seed / 9 % 3)),
    if seed / 27 % 3 = 0 then none else some (seed / 81 % 5)⟩

/-- The source reflection shortcut confuses absent and present numeric zero. -/
def naiveReflection (seed : Nat) : Bool :=
  let a : AddSummary Nat := .atom 41
  let b := a.combine (.number 0)
  let c : AddSummary Nat := .number (seed % 2)
  decide (a.combine c = b.combine c ↔ a = b)

def cancellationCheck (seed : Nat) : Bool :=
  let a := summary seed
  let b := summary (seed / 2 + 19)
  let k := seed / 5 % 7
  let l := seed / 11 % 7
  let numericEq := a.atoms = b.atoms ∧ a.numeric.getD 0 = b.numeric.getD 0
  decide ((a.combine (.number k) = b.combine (.number k) ↔ numericEq) ∧
    (a.combine (.number k) = b.combine (.number k) ↔ a.combine (.number l) = b.combine (.number l)))

def paddingCheck (seed : Nat) : Bool :=
  let a := summary seed
  let k := seed / 3 % 7
  let padded := a.combine (.number 0)
  let incremented := a.combine (.number 1)
  decide (a.combine (.number k) = padded.combine (.number k) ∧
    a.combine (.number k) ≠ incremented.combine (.number k))

#eval campaign "enriched-frame numeric reflection (negative control)"
  (∀ n : Nat, naiveReflection n = true) 1 true
#eval do
  for seed in [1, 7, 42] do
    campaign "numeric-offset cancellation with optional zero presence"
      (∀ n : Nat, cancellationCheck n = true ∧ paddingCheck n = true) seed
  unless (List.range 256).all (fun n => cancellationCheck n && paddingCheck n) do
    throw (IO.userError "numeric-reflection backstop failed")
  IO.println "numeric-reflection backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.NumericReflectionExperiments
