import ExplainableCrypto.Helios.Computational.PrimeSimCommitSource


/-! Source identity for the second coordinate of the zero-message branch.
The concrete caller reuses the existing two-power/product controller with
public-key and second-ciphertext operands. -/
namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitSecondSource

/-- The zero-message term vanishes in the actual simulated branch. -/
theorem second_group {p q : Nat} [Fact q.Prime]
    (stmt : BallotStatement (PrimeGroup p q)) (c e z0 z1 : ZMod q) :
    (ballotSimCommit stmt c (e,z0,z1)).1.2 =
      z0 • stmt.publicKey - e • stmt.ciphertext.2 := by
  change z0 • stmt.publicKey - e • (stmt.ciphertext.2 - (0 : ZMod q) • stmt.generator) = _
  rw [zero_smul,sub_zero]

/-- Subgroup complement action gives the same executed exponent as coordinate one. -/
theorem second_coordinate {p q : Nat} [Fact q.Prime]
    (stmt : BallotStatement (PrimeGroup p q)) (c e z0 z1 : ZMod q) :
    primeGroupCoordinate (ballotSimCommit stmt c (e,z0,z1)).1.2 =
      primeGroupCoordinate stmt.publicKey ^ z0.val *
        primeGroupCoordinate stmt.ciphertext.2 ^ (q-e.val) := by
  rw [second_group,sub_eq_add_neg,←neg_smul,primeGroupCoordinate_add,
    primeGroupCoordinate_smul,primeGroupCoordinate_smul,
    PrimeSimCommitSource.complement_action]

/-- The actual second commitment matches the existing modular power/product API.
Only the typed subgroup law is needed; prime p or exact order is not assumed. -/
theorem second_coordinate_value {p q : Nat} [NeZero p] [Fact q.Prime]
    (stmt : BallotStatement (PrimeGroup p q)) (c e z0 z1 : ZMod q) :
    (primeGroupCoordinate (ballotSimCommit stmt c (e,z0,z1)).1.2).val =
      (((primeGroupCoordinate stmt.publicKey).val^z0.val % p) *
        ((primeGroupCoordinate stmt.ciphertext.2).val^(q-e.val) % p)) % p := by
  rw [second_coordinate,ZMod.val_mul]
  have hk : (primeGroupCoordinate stmt.publicKey ^ z0.val).val =
      (primeGroupCoordinate stmt.publicKey).val ^ z0.val % p := by
    simpa only [Nat.cast_pow,ZMod.natCast_zmod_val] using
      (ZMod.val_natCast p ((primeGroupCoordinate stmt.publicKey).val ^ z0.val))
  have hb : (primeGroupCoordinate stmt.ciphertext.2 ^ (q-e.val)).val =
      (primeGroupCoordinate stmt.ciphertext.2).val ^ (q-e.val) % p := by
    simpa only [Nat.cast_pow,ZMod.natCast_zmod_val] using
      (ZMod.val_natCast p ((primeGroupCoordinate stmt.ciphertext.2).val ^ (q-e.val)))
  rw [hk,hb]

#print axioms second_group
#print axioms second_coordinate
#print axioms second_coordinate_value
end ExplainableCrypto.Helios.Computational.PrimeSimCommitSecondSource
