import ExplainableCrypto.Helios.Computational.ProofReuse
import Mathlib.Algebra.Field.ZMod

/-! Independently calculated small-group fixtures: p=23, q=11, g=2, h=8.
The fixture hash challenge is 5. This tests algorithms, not group hardness or
SHA-256. Scalar values are encoded as powers of 2 to check the concrete group
arithmetic against the abstract constructors. All checks use kernel reduction. -/

namespace ExplainableCrypto.Helios.Computational.Controls

instance : Fact (Nat.Prime 11) := ⟨by decide⟩

abbrev FixtureBranch := Nat × Nat × Nat × Nat
abbrev FixtureProof := FixtureBranch × FixtureBranch

def branchCheck (a b m : Nat) (p : FixtureBranch) : Bool :=
  2 ^ p.2.2.2 % 23 == p.1 * a ^ p.2.2.1 % 23 &&
  8 ^ p.2.2.2 % 23 == p.2.1 * (b * (if m == 0 then 1 else 12) % 23) ^ p.2.2.1 % 23

def proofCheck (a b : Nat) (p : FixtureProof) : Bool :=
  branchCheck a b 0 p.1 && branchCheck a b 1 p.2 &&
  (p.1.2.2.1 + p.2.2.2.1) % 11 == 5

def encodeBranch (p : Branch (ZMod 11) (ZMod 11)) : FixtureBranch :=
  (2 ^ p.a.val % 23, 2 ^ p.b.val % 23, p.challenge.val, p.response.val)

def encodeProof (p : Proof01 (ZMod 11) (ZMod 11)) : FixtureProof :=
  (encodeBranch p.zero, encodeBranch p.one)

def neutralFixture : FixtureProof := ((16, 2, 3, 4), (8, 1, 2, 3))
def zeroFixture : FixtureProof := ((16, 2, 3, 10), (12, 12, 2, 3))
def oneFixture : FixtureProof := ((12, 18, 2, 3), (16, 2, 3, 10))

theorem neutral_constructor_matches :
    encodeProof (neutralProof (fun _ => 5) 1 3 2 3 4) = neutralFixture := by decide

theorem honest_zero_constructor_matches :
    encodeProof (proveZero (fun _ => 5) 1 3 2 4 2 3) = zeroFixture := by decide

theorem honest_one_constructor_matches :
    encodeProof (proveOne (fun _ => 5) 1 3 2 4 2 3) = oneFixture := by decide

theorem neutral_accepted : proofCheck 1 1 neutralFixture = true := by decide
theorem honest_zero_accepted : proofCheck 4 18 zeroFixture = true := by decide
theorem honest_one_accepted : proofCheck 4 13 oneFixture = true := by decide

/-- Change the neutral proof's zero-branch response from 4 to 5. -/
theorem changed_response_rejected :
    proofCheck 1 1 ((16, 2, 3, 5), (8, 1, 2, 3)) = false := by decide

/-- A proof for the neutral ciphertext cannot simply certify this honest one. -/
theorem unrelated_ciphertext_rejected : proofCheck 4 13 neutralFixture = false := by decide

#print axioms neutral_constructor_matches
#print axioms honest_zero_constructor_matches
#print axioms honest_one_constructor_matches
#print axioms neutral_accepted
#print axioms honest_zero_accepted
#print axioms honest_one_accepted
#print axioms changed_response_rejected
#print axioms unrelated_ciphertext_rejected

end ExplainableCrypto.Helios.Computational.Controls
