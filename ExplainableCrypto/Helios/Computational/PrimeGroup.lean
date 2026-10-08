import ExplainableCrypto.Helios.Computational.BallotProof
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Module.Torsion.Free

/-! The historical subgroup as public modular coordinates. The carrier uses
Mathlib's qth roots of unity, never an exposed discrete-log representation. -/
namespace ExplainableCrypto.Helios.Computational

abbrev PrimeGroup (p q : Nat) := Additive (rootsOfUnity q (ZMod p))

/-- Forget only membership proofs, exposing the public residue coordinate. -/
def primeGroupCoordinate {p q : Nat} (x : PrimeGroup p q) : ZMod p := x.toMul.val.val

instance primeGroupModule (p q : Nat) [NeZero q] : Module (ZMod q) (PrimeGroup p q) :=
  AddCommMonoid.zmodModule (fun x => by
    change x.toMul ^ q = 1
    apply Subtype.ext
    exact x.toMul.property)

theorem primeGroupCoordinate_injective {p q : Nat} :
    Function.Injective (primeGroupCoordinate (p := p) (q := q)) :=
  rootsOfUnity.coe_injective

/-- Compare public coordinates directly; membership proofs are irrelevant. -/
instance primeGroupDecidableEq (p q : Nat) : DecidableEq (PrimeGroup p q) :=
  fun x y => decidable_of_iff (primeGroupCoordinate x = primeGroupCoordinate y)
    primeGroupCoordinate_injective.eq_iff

theorem primeGroupCoordinate_zero (p q : Nat) :
    primeGroupCoordinate (0 : PrimeGroup p q) = 1 := rfl

theorem primeGroupCoordinate_add {p q : Nat} (x y : PrimeGroup p q) :
    primeGroupCoordinate (x+y) = primeGroupCoordinate x * primeGroupCoordinate y := rfl

/-- Scalar multiplication in the old additive interface is public modular
exponentiation, with canonical scalar exponent. -/
theorem primeGroupCoordinate_smul {p q : Nat} [NeZero q] (r : ZMod q) (x : PrimeGroup p q) :
    primeGroupCoordinate (r • x) = primeGroupCoordinate x ^ r.val := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q => rfl

theorem primeGroupCoordinate_membership {p q : Nat} (x : PrimeGroup p q) :
    primeGroupCoordinate x ^ q = 1 := by
  exact (mem_rootsOfUnity' q x.toMul.val).mp x.toMul.property

/-- Nonidentity is required of a generator, not of every group element. -/
theorem primeGroup_nonzero_iff {p q : Nat} (g : PrimeGroup p q) :
    g ≠ 0 ↔ primeGroupCoordinate g ≠ 1 := by
  rw [← primeGroupCoordinate_zero p q]
  exact not_congr primeGroupCoordinate_injective.eq_iff.symm

/-- The existing extraction premise follows from a nonidentity generator in
this concrete scalar module. -/
theorem primeGroup_generator_injective {p q : Nat} [Fact q.Prime]
    (g : PrimeGroup p q) (hg : primeGroupCoordinate g ≠ 1) :
    Function.Injective (fun r : ZMod q => r • g) :=
  smul_left_injective (ZMod q) ((primeGroup_nonzero_iff g).mpr hg)

/-- With prime field modulus and a nonidentity generator, the chosen subgroup
has exactly q elements. Cardinality is not an extra caller premise. -/
theorem primeGroup_card {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g : PrimeGroup p q) (hg : primeGroupCoordinate g ≠ 1) :
    Nat.card (PrimeGroup p q) = q := by
  have hl := Nat.card_le_card_of_injective (fun r : ZMod q => r • g) (primeGroup_generator_injective g hg)
  have hu := card_rootsOfUnity (ZMod p) q
  change Nat.card (PrimeGroup p q) ≤ q at hu
  have hq : Nat.card (ZMod q) = q := by simp
  rw [hq] at hl
  exact le_antisymm hu hl

/-- Actual encryptWith specializes to the historical public-coordinate
ElGamal equations, retaining both ciphertext components. -/
theorem primeGroup_encrypt_coordinates {p q : Nat} [Fact q.Prime]
    (g pk : PrimeGroup p q) (r m : ZMod q) :
    (primeGroupCoordinate (encryptWith g pk r m).1,
      primeGroupCoordinate (encryptWith g pk r m).2) =
        (primeGroupCoordinate g ^ r.val,
          primeGroupCoordinate g ^ m.val * primeGroupCoordinate pk ^ r.val) := by
  simp only [encryptWith,primeGroupCoordinate_smul,primeGroupCoordinate_add]

/-- Group negation in the additive interface is inverse of the public field coordinate. -/
theorem primeGroupCoordinate_neg {p q : Nat} [Fact p.Prime] (x : PrimeGroup p q) :
    primeGroupCoordinate (-x) = (primeGroupCoordinate x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← primeGroupCoordinate_add,neg_add_cancel,primeGroupCoordinate_zero]

#print axioms primeGroupCoordinate_neg
#print axioms primeGroupCoordinate_injective
#print axioms primeGroupCoordinate_zero
#print axioms primeGroupCoordinate_add
#print axioms primeGroupCoordinate_smul
#print axioms primeGroupCoordinate_membership
#print axioms primeGroup_nonzero_iff
#print axioms primeGroup_generator_injective
#print axioms primeGroup_card
#print axioms primeGroup_encrypt_coordinates
end ExplainableCrypto.Helios.Computational
