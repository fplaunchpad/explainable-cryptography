import ExplainableCrypto.Helios.Computational.BinaryModMultiplyRun

/-! Independent public-coordinate multiplication fixtures and actual controller
mutations. These controls retain complete work/operand states and bit order. -/
namespace ExplainableCrypto.Helios.Computational.BinaryModMultiplyControls
open BinaryModMultiply
set_option maxRecDepth 65536
set_option synthInstance.maxSize 512

def trace (p x : Nat) (raw : List Bool) : Config :=
  tick^[clock p raw.length] (start x.bits raw p.bits)

/-- 4*13 mod23=6; the source's nonpalindromic little-endian word is 1011. -/
theorem product_control : trace 23 4 [true,false,true,true] =
    (⟨none,2, ![[false,true,true],[],[],[],[],[],[true,true,true,false,true],[],[],[],[false,false,true]]⟩ : Config) := by
  rw [trace,padded_run 23 4 _ (by decide)]
  rfl

/-- High zero padding leaves the represented product unchanged. -/
theorem padded_control : trace 23 4 [true,false,true,true,false,false] =
    result [false,true,true] [false,false,true] [true,true,true,false,true] := by
  rw [trace,padded_run 23 4 _ (by decide)]
  rfl

/-- Empty multiplication still derives and cleans its complement. -/
theorem empty_control : trace 23 4 [] =
    (⟨none,2, ![[],[],[],[],[],[],[true,true,true,false,true],[],[],[],[false,false,true]]⟩ : Config) := by
  rw [trace,padded_run 23 4 _ (by decide)]
  rfl

/-- Modulus one includes only multiplicand zero and yields canonical empty digits. -/
theorem modulus_one_control : trace 1 0 [true,true,false,true] =
    result [] [] [true] := by
  rw [trace,padded_run 1 0 _ (by decide)]
  rfl

/-- Coordinate arithmetic uses public modulus23, not subgroup-order11. -/
theorem not_scalar_modulus : (trace 23 4 [true,false,true,true]).stk 0 ≠ [false,false,false,true] := by
  rw [product_control]
  decide +kernel

private def mutated (m : Nat) (l : Fin 86) :=
  if m == 1 && l == copyLabel 0 then enter (prepLabel 0)
  else if m == 2 && l == 5 then move 3 0 5 1
  else if m == 3 && l == doubleLabel false 4 then enter (doubleLabel false 0)
  else if m == 3 && l == doubleLabel true 4 then enter (doubleLabel true 0)
  else if m == 4 && l == 8 then .load (fun _ => 2) .halt
  else if m == 5 && l == 0 then enter 1
  else if m == 5 && l == 1 then
    TM2FiniteCoordinates.translate (Equiv.swap (8 : Fin 11) 9) (Equiv.refl _) (Equiv.refl _) (control 1)
  else program l

private def mutantReadout (m : Nat) :=
  let out := (TM2ReturnLink.tick (mutated m))^[600]
    (start [false,false,true] [true,false,true,true] [true,true,true,false,true])
  (out.l,out.var.val,out.stk 0,out.stk 1,out.stk 6,out.stk 8,out.stk 10)

/-- Omitting the actual modulus copy rejects before any multiplier iteration. -/
theorem omitted_preparation_counterexample : mutantReadout 1 =
    (none,1,[],[],[true,true,true,false,true],[true,false,true,true],[false,false,true]) := by
  decide +kernel

/-- Skipping addition for one bits yields zero for the positive product. -/
theorem omitted_addition_counterexample : mutantReadout 2 =
    (none,2,[],[],[true,true,true,false,true],[],[false,false,true]) := by
  decide +kernel

/-- Without doubling, three one bits give 3*4=12 instead of 13*4 mod23=6. -/
theorem omitted_doubling_counterexample : mutantReadout 3 =
    (none,2,[false,false,true,true],[],[true,true,true,false,true],[],[false,false,true]) := by
  decide +kernel

/-- A correct product alone misses failure to clear the prepared complement19. -/
theorem retained_complement_counterexample : mutantReadout 4 =
    (none,2,[false,true,true],[true,true,false,false,true],[true,true,true,false,true],[],[false,false,true]) := by
  decide +kernel

/-- Reading the same bits least-significant-first computes 4*11 mod23=21. -/
theorem bit_order_counterexample : mutantReadout 5 =
    (none,2,[true,false,true,false,true],[],[true,true,true,false,true],[],[false,false,true]) := by
  decide +kernel

#print axioms product_control
#print axioms padded_control
#print axioms empty_control
#print axioms modulus_one_control
#print axioms not_scalar_modulus
#print axioms omitted_preparation_counterexample
#print axioms omitted_addition_counterexample
#print axioms omitted_doubling_counterexample
#print axioms retained_complement_counterexample
#print axioms bit_order_counterexample
end ExplainableCrypto.Helios.Computational.BinaryModMultiplyControls
