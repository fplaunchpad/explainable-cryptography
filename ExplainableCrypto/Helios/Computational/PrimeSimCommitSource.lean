import Mathlib.Data.Nat.Size
import ExplainableCrypto.Helios.Computational.PrimeGroup
import ExplainableCrypto.Helios.Computational.BallotSigmaSimulation


/-! First simulated commitment as public-coordinate powers and product.
The enclosing controller owns scalar parsing, complement subtraction and frames. -/
namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitSource

/-- Actual first commitment, retaining the source's negative scalar action. -/
theorem first_coordinate_negative {p q : Nat} [Fact q.Prime]
    (stmt : BallotStatement (PrimeGroup p q)) (c e z0 z1 : ZMod q) :
    primeGroupCoordinate (ballotSimCommit stmt c (e,z0,z1)).1.1 =
      primeGroupCoordinate stmt.generator ^ z0.val *
        primeGroupCoordinate stmt.ciphertext.1 ^ (-e).val := by
  change primeGroupCoordinate (z0 • stmt.generator - e • stmt.ciphertext.1) = _
  rw [sub_eq_add_neg,←neg_smul,primeGroupCoordinate_add,primeGroupCoordinate_smul,
    primeGroupCoordinate_smul]

/-- Subgroup membership permits exponent q at zero without a runtime zero branch.
Mere nonzero public residues would not justify this equality. -/
theorem complement_action {p q : Nat} [NeZero q] (alpha : PrimeGroup p q) (e : ZMod q) :
    primeGroupCoordinate alpha ^ (-e).val = primeGroupCoordinate alpha ^ (q-e.val) := by
  by_cases he : e = 0
  · subst e
    simp only [neg_zero,ZMod.val_zero,Nat.sub_zero,pow_zero]
    exact (primeGroupCoordinate_membership alpha).symm
  · let : NeZero e := ⟨he⟩
    rw [ZMod.val_neg_of_ne_zero]

/-- Two public powers and their product give the actual first commitment.
Only the typed q-root subgroup law is used; exact order is not assumed. -/
theorem first_coordinate {p q : Nat} [Fact q.Prime]
    (stmt : BallotStatement (PrimeGroup p q)) (c e z0 z1 : ZMod q) :
    primeGroupCoordinate (ballotSimCommit stmt c (e,z0,z1)).1.1 =
      primeGroupCoordinate stmt.generator ^ z0.val *
        primeGroupCoordinate stmt.ciphertext.1 ^ (q-e.val) := by
  rw [first_coordinate_negative,complement_action]

/-- Canonical residue values match the existing modular power/multiply interfaces. -/
theorem first_coordinate_value {p q : Nat} [NeZero p] [Fact q.Prime]
    (stmt : BallotStatement (PrimeGroup p q)) (c e z0 z1 : ZMod q) :
    (primeGroupCoordinate (ballotSimCommit stmt c (e,z0,z1)).1.1).val =
      (((primeGroupCoordinate stmt.generator).val^z0.val % p) *
        ((primeGroupCoordinate stmt.ciphertext.1).val^(q-e.val) % p)) % p := by
  rw [first_coordinate,ZMod.val_mul]
  have hg : (primeGroupCoordinate stmt.generator ^ z0.val).val =
      (primeGroupCoordinate stmt.generator).val ^ z0.val % p := by
    simpa only [Nat.cast_pow,ZMod.natCast_zmod_val] using
      (ZMod.val_natCast p ((primeGroupCoordinate stmt.generator).val ^ z0.val))
  have ha : (primeGroupCoordinate stmt.ciphertext.1 ^ (q-e.val)).val =
      (primeGroupCoordinate stmt.ciphertext.1).val ^ (q-e.val) % p := by
    simpa only [Nat.cast_pow,ZMod.natCast_zmod_val] using
      (ZMod.val_natCast p ((primeGroupCoordinate stmt.ciphertext.1).val ^ (q-e.val)))
  rw [hg,ha]

/-- The complement may equal q; its executed power clock therefore uses q.size. -/
theorem complement_width {q : Nat} (e : ZMod q) : (q-e.val).size ≤ q.size :=
  Nat.size_le_size (Nat.sub_le q e.val)

#print axioms first_coordinate_negative
#print axioms complement_action
#print axioms first_coordinate
#print axioms first_coordinate_value
#print axioms complement_width
end ExplainableCrypto.Helios.Computational.PrimeSimCommitSource
