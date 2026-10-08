import ExplainableCrypto.Helios.Computational.PrimeGroup
import ExplainableCrypto.Helios.Computational.ScalarCodec

/-! Canonical public-coordinate records for the historical prime subgroup.
The internal decoder retains identity and checks membership; it is not yet the
election's complete raw-input parser. -/
namespace ExplainableCrypto.Helios.Computational

/-- Encode the public field coordinate using the existing canonical scalar codec. -/
def primeGroupEncode {p q : Nat} (x : PrimeGroup p q) : List Bool :=
  scalarEncode (primeGroupCoordinate x)

/-- Parse the public residue and check qth-root membership. Constructing the
unit uses Mathlib's explicit power-based inverse, never a discrete logarithm. -/
def primeGroupDecode (p q : Nat) [NeZero q] (word : List Bool) : Option (PrimeGroup p q) :=
  match scalarDecode p word with
  | none => none
  | some a => if h : a^q = 1 then some (Additive.ofMul (rootsOfUnity.mkOfPowEq a h)) else none

/-- Every typed group element, including identity, round-trips. -/
theorem primeGroupDecode_encode {p q : Nat} [NeZero p] [NeZero q] (x : PrimeGroup p q) :
    primeGroupDecode p q (primeGroupEncode x) = some x := by
  unfold primeGroupDecode primeGroupEncode
  rw [scalarDecode_encode]
  dsimp only
  rw [dif_pos (primeGroupCoordinate_membership x)]
  congr 1
  apply primeGroupCoordinate_injective
  rfl

/-- Successful parsing identifies the exact original canonical word. -/
theorem primeGroupDecode_exact {p q : Nat} [NeZero q] (word : List Bool) (x : PrimeGroup p q)
    (h : primeGroupDecode p q word = some x) : word = primeGroupEncode x := by
  unfold primeGroupDecode at h
  cases ha : scalarDecode p word with
  | none => simp [ha] at h
  | some a =>
    rw [ha] at h
    dsimp only at h
    by_cases hm : a^q = 1
    · rw [dif_pos hm] at h
      cases Option.some.inj h
      change word = scalarEncode a
      exact scalarDecode_exact word a ha
    · rw [dif_neg hm] at h
      cases h

/-- Public coordinate encoding is injective, without revealing a generator exponent. -/
theorem primeGroupEncode_injective {p q : Nat} [NeZero p] [NeZero q] :
    Function.Injective (primeGroupEncode (p := p) (q := q)) := by
  intro x y h
  have he := congrArg (primeGroupDecode p q) h
  rw [primeGroupDecode_encode,primeGroupDecode_encode] at he
  exact Option.some.inj he

/-- The actual record length is controlled by the public field-modulus width. -/
theorem primeGroupEncode_length_le {p q : Nat} [NeZero p] (x : PrimeGroup p q) :
    (primeGroupEncode x).length ≤ 2*(p-1).size+1 :=
  scalarEncode_length_le _

/-- A canonical residue outside the subgroup is not a group record. -/
theorem primeGroupDecode_nonmember {p q : Nat} [NeZero p] [NeZero q]
    (a : ZMod p) (ha : a^q ≠ 1) : primeGroupDecode p q (scalarEncode a) = none := by
  simp [primeGroupDecode,scalarDecode_encode,ha]

/-- Out-of-range words cannot be accepted by reducing them modulo p. -/
theorem primeGroupDecode_outOfRange (p q n : Nat) [NeZero q] (hn : p ≤ n) :
    primeGroupDecode p q (uniformNatEncode n) = none := by
  have hr := uniformNatRead_encode n []
  simp only [List.append_nil] at hr
  simp [primeGroupDecode,scalarDecode,hr,not_lt.mpr hn]

#print axioms primeGroupDecode_encode
#print axioms primeGroupDecode_exact
#print axioms primeGroupEncode_injective
#print axioms primeGroupEncode_length_le
#print axioms primeGroupDecode_nonmember
#print axioms primeGroupDecode_outOfRange
end ExplainableCrypto.Helios.Computational
