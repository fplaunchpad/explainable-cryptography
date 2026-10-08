import ExplainableCrypto.Helios.Computational.UniformOperandCodec

/-! Arithmetic obligations for the loaded square-and-multiply controller.
The modulus p reduces public coordinates; this file makes no operational claim. -/
namespace ExplainableCrypto.Helios.Computational.BinaryModPowerArithmetic

def step (p base a : Nat) (b : Bool) : Nat :=
  if b then (((a*a)%p)*base)%p else (a*a)%p

/-- Either controller branch produces a reduced accumulator. -/
theorem step_lt (p base a : Nat) (b : Bool) (hp : 0 < p) : step p base a b < p := by
  cases b <;> exact Nat.mod_lt _ hp

private theorem square_pow (p base n : Nat) :
    ((base^n%p)*(base^n%p))%p = base^(2*n)%p := by
  rw [← Nat.mul_mod,← Nat.pow_add,Nat.two_mul]

/-- Squaring and conditional multiplication extend the interpreted exponent
prefix by exactly its next most-significant-first bit. -/
theorem step_pow (p base n : Nat) (b : Bool) :
    step p base (base^n%p) b = base^(Nat.bit b n)%p := by
  cases b
  · simpa [step,Nat.bit_val] using square_pow p base n
  · change ((((base^n%p)*(base^n%p))%p)*base)%p = base^(Nat.bit true n)%p
    rw [square_pow,Nat.mod_mul_mod]
    simp [Nat.bit_val,Nat.pow_succ]

private theorem fold_prefix (p base n : Nat) (word : List Bool) :
    word.foldl (step p base) (base^n%p) =
      base^(word.foldl (fun a b => Nat.bit b a) n)%p := by
  induction word generalizing n with
  | nil => rfl
  | cons b word ih =>
    simp only [List.foldl_cons,step_pow]
    exact ih (Nat.bit b n)

/-- The initial literal one is reduced when p>=2. Empty exponent words and
arbitrary high zero padding are included without a positivity premise on base. -/
theorem fold_reverse_one (p base : Nat) (raw : List Bool) (hp : 2 ≤ p) :
    raw.reverse.foldl (step p base) 1 = base^bitsValue raw%p := by
  have hone : 1%p = 1 := Nat.mod_eq_of_lt (by omega)
  simpa [List.foldl_reverse,bitsValue,hone] using fold_prefix p base 0 raw.reverse

/-- Empty exponent yields the multiplicative identity, including for base zero. -/
theorem empty_control : ([] : List Bool).reverse.foldl (step 23 0) 1 = 1 := by decide +kernel

/-- Little-endian 1011 represents thirteen; 4^13 mod23 is sixteen. -/
theorem power_control :
    ([true,false,true,true] : List Bool).reverse.foldl (step 23 4) 1 = 16 := by decide +kernel

theorem padded_control :
    ([true,false,true,true,false,false] : List Bool).reverse.foldl (step 23 4) 1 = 16 := by decide +kernel

/-- The coordinate modulus remains23, not the scalar order11. -/
theorem not_scalar_modulus :
    ([true,false,true,true] : List Bool).reverse.foldl (step 23 4) 1 ≠ 9 := by decide +kernel

/-- The smallest positive nonidentity gate witness: reading raw10 directly
interprets exponent two rather than its little-endian value one. -/
theorem wrong_order_counterexample :
    ([true,false] : List Bool).foldl (step 3 2) 1 = 1 ∧
      ([true,false] : List Bool).reverse.foldl (step 3 2) 1 = 2 := by decide +kernel

/-- Omitting squaring loses the second-place exponent bit. This mutation is
of the arithmetic candidate, not of an operational controller. -/
theorem omitted_square_counterexample :
    ([false,true] : List Bool).reverse.foldl (fun a b => if b then a*2%3 else a) 1 = 2 ∧
      ([false,true] : List Bool).reverse.foldl (step 3 2) 1 = 1 := by decide +kernel

/-- Squaring alone stays at one on a nonzero exponent and nonidentity base. -/
theorem omitted_multiply_counterexample :
    ([true] : List Bool).reverse.foldl (fun a _ => a*a%3) 1 = 1 ∧
      ([true] : List Bool).reverse.foldl (step 3 2) 1 = 2 := by decide +kernel

#print axioms step_lt
#print axioms step_pow
#print axioms fold_reverse_one
#print axioms empty_control
#print axioms power_control
#print axioms padded_control
#print axioms not_scalar_modulus
#print axioms wrong_order_counterexample
#print axioms omitted_square_counterexample
#print axioms omitted_multiply_counterexample
end ExplainableCrypto.Helios.Computational.BinaryModPowerArithmetic
