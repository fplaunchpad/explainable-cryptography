import ExplainableCrypto.Helios.Computational.UniformOperandCodec

/-! Arithmetic obligations for the scoped modular multiplier controller.
These lemmas do not claim execution or supply an assumed machine certificate. -/
namespace ExplainableCrypto.Helios.Computational.BinaryModMultiplyArithmetic

/-- The controller uses the complement as its guarded subtraction threshold. -/
def reducedAdd (m x r : Nat) : Nat :=
  if m-x ≤ r then r-(m-x) else m-((m-x)-r)

/-- Both guarded-subtraction routes compute the same canonical modular sum. -/
theorem reducedAdd_eq_mod (m x r : Nat) (hx : x < m) (hr : r < m) :
    reducedAdd m x r = (r+x)%m := by
  unfold reducedAdd
  split_ifs with h
  · have hs : r-(m-x) = r+x-m := by omega
    have hm : m ≤ r+x := by omega
    have hb : r+x-m < m := by omega
    rw [hs,Nat.mod_eq_sub_mod hm,Nat.mod_eq_of_lt hb]
  · have hs : m-((m-x)-r) = r+x := by omega
    have hb : r+x < m := by omega
    rw [hs,Nat.mod_eq_of_lt hb]

theorem reducedAdd_lt (m x r : Nat) (hx : x < m) (hr : r < m) :
    reducedAdd m x r < m := by
  rw [reducedAdd_eq_mod m x r hx hr]
  exact Nat.mod_lt _ (by omega)

/-- The complement is positive, and each natural subtraction operand/result
used by the add controller is bounded by the retained modulus and its width. -/
theorem operand_bounds (m x r : Nat) (hx : x < m) (hr : r < m) :
    0 < m-x ∧ m-x ≤ m ∧ (m-x).size ≤ m.size ∧
    (m-x)-r ≤ m ∧ ((m-x)-r).size ≤ m.size ∧
    r-(m-x) ≤ m ∧ (r-(m-x)).size ≤ m.size ∧
    m-((m-x)-r) ≤ m ∧ (m-((m-x)-r)).size ≤ m.size := by
  have hc : m-x ≤ m := Nat.sub_le _ _
  have hd : (m-x)-r ≤ m := (Nat.sub_le _ _).trans hc
  have he : r-(m-x) ≤ m := (Nat.sub_le _ _).trans hr.le
  have hf : m-((m-x)-r) ≤ m := Nat.sub_le _ _
  exact ⟨by omega,hc,Nat.size_le_size hc,hd,Nat.size_le_size hd,
    he,Nat.size_le_size he,hf,Nat.size_le_size hf⟩

/-- On underflow, both subsequent subtractions are legitimate and the first
difference is positive; the final result therefore remains below m. -/
theorem underflow_bounds (m x r : Nat) (hx : x < m) (h : r < m-x) :
    r ≤ m-x ∧ 0 < (m-x)-r ∧ (m-x)-r ≤ m ∧ m-((m-x)-r) < m := by
  omega

/-- One most-significant-first multiplier update. -/
def step (m x a : Nat) (b : Bool) : Nat :=
  ((2*a)%m + if b then x else 0)%m

theorem step_lt (m x a : Nat) (b : Bool) (hm : 0 < m) : step m x a b < m :=
  Nat.mod_lt _ hm

/-- The actual guarded addition is required only when the multiplier bit is one. -/
theorem step_reducedAdd (m x a : Nat) (b : Bool) (hx : x < m) :
    step m x a b = if b then reducedAdd m x ((2*a)%m) else (2*a)%m := by
  cases b
  · simp [step]
  · simp only [step,ite_true]
    exact (reducedAdd_eq_mod m x _ hx (Nat.mod_lt _ (by omega))).symm

/-- This is the induction step for the interpreted consumed multiplier prefix. -/
theorem step_mul_bit (m x n : Nat) (b : Bool) :
    step m x ((x*n)%m) b = (x*Nat.bit b n)%m := by
  cases b
  · simp [step,Nat.bit_val,Nat.mul_left_comm]
  · simp only [step,ite_true,Nat.mod_add_mod,Nat.bit_val,Bool.toNat_true]
    rw [Nat.add_mod,Nat.mul_mod_mod,← Nat.add_mod]
    simp [Nat.mul_add,Nat.mul_left_comm]

private theorem fold_prefix (m x n : Nat) (word : List Bool) :
    word.foldl (step m x) ((x*n)%m) =
      (x*word.foldl (fun a b => Nat.bit b a) n)%m := by
  induction word generalizing n with
  | nil => rfl
  | cons b word ih =>
    simp only [List.foldl_cons,step_mul_bit]
    exact ih (Nat.bit b n)

/-- Reversing the loaded little-endian word supplies the controller's MSB-first
order. High zero padding and the empty word are included. -/
theorem fold_reverse_zero (m x : Nat) (raw : List Bool) :
    raw.reverse.foldl (step m x) 0 = (x*bitsValue raw)%m := by
  simpa [List.foldl_reverse,bitsValue] using fold_prefix m x 0 raw.reverse

theorem wrap_control : reducedAdd 2 1 1 = 0 := by decide +kernel
theorem no_wrap_control : reducedAdd 11 3 2 = 5 := by decide +kernel
theorem product_control :
    ([true,false,false,true] : List Bool).reverse.foldl (step 23 4) 0 = 13 := by decide +kernel

/-- Replacing the successful guard's ≤ by < returns the noncanonical modulus
at the smallest equality boundary. -/
theorem strict_threshold_counterexample :
    (if 2-1 < 1 then 1-(2-1) else 2-((2-1)-1) : Nat) = 2 ∧
      reducedAdd 2 1 1 ≠ 2 := by decide +kernel

/-- Reversing the successful subtraction operands loses a nonzero residue. -/
theorem reversed_operands_counterexample :
    (if 3-2 ≤ 2 then (3-2)-2 else 3-((3-2)-2) : Nat) = 0 ∧
      reducedAdd 3 2 2 = 1 := by decide +kernel

#print axioms reducedAdd_eq_mod
#print axioms reducedAdd_lt
#print axioms operand_bounds
#print axioms underflow_bounds
#print axioms step_lt
#print axioms step_reducedAdd
#print axioms step_mul_bit
#print axioms fold_reverse_zero
#print axioms wrap_control
#print axioms no_wrap_control
#print axioms product_control
#print axioms strict_threshold_counterexample
#print axioms reversed_operands_counterexample
end ExplainableCrypto.Helios.Computational.BinaryModMultiplyArithmetic
