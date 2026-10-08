import Mathlib.Algebra.Field.ZMod
import ExplainableCrypto.Helios.Computational.ElectionDDHConstruction
import ExplainableCrypto.Helios.Computational.BallotProgrammedOracle

/-! Exponent-form checks of the independent order-11 subgroup modulo 23
fixture. The small field is an arithmetic control, not a hardness instance. -/
namespace ExplainableCrypto.Helios.Computational.ElectionDDHConstructionControls
open ElectionDDHConstruction
local instance : Fact (Nat.Prime 11) := ⟨by decide +kernel⟩
abbrev Scalar := ZMod 11

/-- Independent multiplicative fixture: g=2, pk=8 modulo 23. These pairs
are discrete-log exponents used only to validate the formal equations. -/
theorem real_fixture :
    paired (F := Scalar) (1 : Scalar) 3 1 3 5 2 5 false =
      ((![(1,3),(2,6)],![(4,2),(5,4)]),![5,7]) := by decide +kernel

/-- Nonzero original nonces 1 and 10 have zero combined nonce. -/
theorem zero_combined_nonce :
    original (F := Scalar) (1 : Scalar) 3 1 2 10 5 false = paired (F := Scalar) 1 3 1 3 0 2 5 false ∧
    (1 : Scalar) ≠ 0 ∧ (10 : Scalar) ≠ 0 ∧ (1 + 10 : Scalar) = 0 := by
  decide +kernel

/-- A random challenge still cancels; neither proof nor secrecy is inferred. -/
theorem arbitrary_challenge_totals :
    let out := paired (F := Scalar) (1 : Scalar) 3 1 7 5 2 5 false
    out.1.1 0 + out.1.2 0 = (5,5) ∧ out.1.1 1 + out.1.2 1 = (7,10) := by
  decide +kernel

/-- Adding the challenge instead of subtracting it changes the public total. -/
theorem addition_mutant_changes_total :
    (1,3) + (encryptWith (F := Scalar) (1 : Scalar) 3 5 1 + (1,3)) ≠ (5,5) := by
  decide +kernel

/-- Omitting the accepted malicious nonce 6 loses the cancellation in column 0. -/
theorem malicious_nonce_required :
    let out := paired (F := Scalar) (1 : Scalar) 3 1 3 5 2 5 false
    let tally := out.1.1 0 + out.1.2 0 + encryptWith (F := Scalar) 1 3 6 0
    partialDecrypt (3 : Scalar) tally = 0 ∧
    out.2 0 • (3 : Scalar) ≠ partialDecrypt (3 : Scalar) tally := by
  decide +kernel

/-- A dummy zero-vote witness cannot stand for this supplied challenge statement. -/
theorem dummy_statement_differs :
    (⟨1,3,(1,7)⟩ : BallotStatement Scalar) ≠ honestProofStatement (F := Scalar) 1 3 (false,0) := by
  decide +kernel

#print axioms real_fixture
#print axioms zero_combined_nonce
#print axioms arbitrary_challenge_totals
#print axioms addition_mutant_changes_total
#print axioms malicious_nonce_required
#print axioms dummy_statement_differs
end ExplainableCrypto.Helios.Computational.ElectionDDHConstructionControls
