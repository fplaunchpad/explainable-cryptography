import ExplainableCrypto.Helios.Computational.PrimeSimCommitSource

/-! Exact source operands for the two remaining one-message commitments.
These equations do not execute scalar subtraction or adjusted-beta construction. -/
namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitOneSource

theorem first_group {p q : Nat} [Fact q.Prime]
    (stmt : BallotStatement (PrimeGroup p q)) (c e z0 z1 : ZMod q) :
    (ballotSimCommit stmt c (e,z0,z1)).2.1 =
      z1 • stmt.generator - (c-e) • stmt.ciphertext.1 := rfl

theorem second_group {p q : Nat} [Fact q.Prime]
    (stmt : BallotStatement (PrimeGroup p q)) (c e z0 z1 : ZMod q) :
    (ballotSimCommit stmt c (e,z0,z1)).2.2 =
      z1 • stmt.publicKey - (c-e) • (stmt.ciphertext.2-stmt.generator) := by
  change z1 • stmt.publicKey - (c-e) • (stmt.ciphertext.2-(1 : ZMod q) • stmt.generator) = _
  rw [one_smul]

private theorem action_value {p q : Nat} [NeZero p] [Fact q.Prime]
    (g alpha : PrimeGroup p q) (e z : ZMod q) :
    (primeGroupCoordinate (z • g - e • alpha)).val =
      (((primeGroupCoordinate g).val^z.val % p) *
        ((primeGroupCoordinate alpha).val^(q-e.val) % p)) % p :=
  PrimeSimCommitSource.first_coordinate_value ⟨g,g,(alpha,alpha)⟩ 0 e z 0

/-- The actual one-branch challenge is c-e, with its canonical residue. -/
theorem first_coordinate_value {p q : Nat} [NeZero p] [Fact q.Prime]
    (stmt : BallotStatement (PrimeGroup p q)) (c e z0 z1 : ZMod q) :
    (primeGroupCoordinate (ballotSimCommit stmt c (e,z0,z1)).2.1).val =
      (((primeGroupCoordinate stmt.generator).val^z1.val % p) *
        ((primeGroupCoordinate stmt.ciphertext.1).val^(q-(c-e).val) % p)) % p := by
  rw [first_group,action_value]

/-- The second one-branch operand is beta-g as an actual typed group element. -/
theorem second_coordinate_value {p q : Nat} [NeZero p] [Fact q.Prime]
    (stmt : BallotStatement (PrimeGroup p q)) (c e z0 z1 : ZMod q) :
    (primeGroupCoordinate (ballotSimCommit stmt c (e,z0,z1)).2.2).val =
      (((primeGroupCoordinate stmt.publicKey).val^z1.val % p) *
        ((primeGroupCoordinate (stmt.ciphertext.2-stmt.generator)).val^(q-(c-e).val) % p)) % p := by
  rw [second_group,action_value]

/-- Modular subtraction includes the underflow case, unlike truncated Nat subtraction. -/
theorem difference_value {q : Nat} [NeZero q] (c e : ZMod q) :
    (c-e).val = (c.val+q-e.val)%q := by
  have he : e.val ≤ c.val+q := by have := ZMod.val_lt e; omega
  have hcast : ((c.val+q-e.val : Nat) : ZMod q) = c-e := by
    rw [Nat.cast_sub he]
    simp
  rw [←hcast,ZMod.val_natCast]

/-- Adjusted beta can be constructed using an existing power and product;
q-root membership justifies exponent q-1 even without an exact-order premise. -/
theorem adjusted_beta_value {p q : Nat} [NeZero p] [Fact q.Prime]
    (beta g : PrimeGroup p q) :
    (primeGroupCoordinate (beta-g)).val =
      ((primeGroupCoordinate beta).val * ((primeGroupCoordinate g).val^(q-1)%p))%p := by
  have ho : (1 : ZMod q).val = 1 := by
    rw [ZMod.val_one_eq_one_mod,Nat.mod_eq_of_lt (Fact.out : q.Prime).one_lt]
  simpa only [one_smul,ho,pow_one,Nat.mod_eq_of_lt (ZMod.val_lt _)] using
    action_value beta g (1 : ZMod q) (1 : ZMod q)

theorem scalar_widths {q : Nat} [NeZero q] (c e z1 : ZMod q) :
    (c-e).val.size ≤ q.size ∧ z1.val.size ≤ q.size ∧
      (q-(c-e).val).size ≤ q.size :=
  ⟨Nat.size_le_size (Nat.le_of_lt (ZMod.val_lt _)),
    Nat.size_le_size (Nat.le_of_lt (ZMod.val_lt _)),
    PrimeSimCommitSource.complement_width (c-e)⟩

theorem adjusted_beta_width {p q : Nat} [NeZero p] [Fact q.Prime]
    (beta g : PrimeGroup p q) : (primeGroupCoordinate (beta-g)).val.size ≤ p.size :=
  Nat.size_le_size (Nat.le_of_lt (ZMod.val_lt _))

#print axioms first_group
#print axioms second_group
#print axioms first_coordinate_value
#print axioms second_coordinate_value
#print axioms difference_value
#print axioms adjusted_beta_value
#print axioms scalar_widths
#print axioms adjusted_beta_width
end ExplainableCrypto.Helios.Computational.PrimeSimCommitOneSource
