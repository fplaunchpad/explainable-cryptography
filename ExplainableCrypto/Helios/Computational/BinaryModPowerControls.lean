import ExplainableCrypto.Helios.Computational.BinaryModPowerRun

/-! Literal executed controls for modular power, including actual-code mutants.
Expected powers are calculated independently; saved exponent/context are checked
separately from the arithmetic output. -/
namespace ExplainableCrypto.Helios.Computational.BinaryModPowerControls
open BinaryModPower
set_option maxRecDepth 262144
set_option synthInstance.maxSize 512

private def mutated (m : Nat) (l : Fin 192) :=
  if m == 1 && l == 1 then .push 0 (fun _ => false) (enter 2)
  else if m == 2 && l == 2 then
    .peek 12 (fun _ b => BinaryModuloCode.memory b)
      (.branch (fun v => v == 0) (.load (fun _ => 2) .halt) (enter 6))
  else if m == 3 && l == 6 then
    .pop 12 (fun _ b => BinaryModuloCode.memory b) (enter 2)
  else if m == 4 && l == 1 then .push 13 (fun _ => false) (control 1)
  else if m == 5 && l == 0 then enter 1
  else if m == 5 && (l == copyLabel 0 0 || l == copyLabel 0 1) then
    TM2FiniteCoordinates.translate (Equiv.swap (8 : Fin 15) 12) (Equiv.refl _) (Equiv.refl _) (program l)
  else if m == 6 && l == 1 then .push 14 (fun _ => false) (control 1)
  else program l

private def readout (m : Nat) (raw : List Bool) :=
  let out := (TM2ReturnLink.tick (mutated m))^[2100]
    (start [false,false,true] raw [true,true,true,false,true] [true,false,true])
  (out.l,out.var.val,out.stk 0,out.stk 6,out.stk 11,out.stk 13,out.stk 14)

/-- 4^13 mod23=16 with unchanged public operands, exponent and context. -/
theorem power_control : readout 0 [true,false,true,true] =
    (none,2,[false,false,false,false,true],[true,true,true,false,true],
      [false,false,true],[true,false,true,true],[true,false,true]) := by decide +kernel

/-- Exponent zero returns one while retaining all original input records. -/
theorem empty_control : readout 0 [] =
    (none,2,[true],[true,true,true,false,true],[false,false,true],[],[true,false,true]) := by decide +kernel

/-- Literal zero initialization returns a noncanonical zero for exponent zero. -/
theorem zero_initialization_counterexample : readout 1 [] =
    (none,2,[false],[true,true,true,false,true],[false,false,true],[],[true,false,true]) := by decide +kernel

/-- Without squaring the three one bits yield 4^3 mod23=18. -/
theorem omitted_square_counterexample : readout 2 [true,false,true,true] =
    (none,2,[false,true,false,false,true],[true,true,true,false,true],
      [false,false,true],[true,false,true,true],[true,false,true]) := by decide +kernel

/-- Repeatedly squaring one cannot replace one-bit base multiplication. -/
theorem omitted_multiply_counterexample : readout 3 [true,false,true,true] =
    (none,2,[true],[true,true,true,false,true],
      [false,false,true],[true,false,true,true],[true,false,true]) := by decide +kernel

/-- Correct numeric output does not justify corruption of the saved exponent. -/
theorem corrupted_exponent_counterexample : readout 4 [true,false,true,true] =
    (none,2,[false,false,false,false,true],[true,true,true,false,true],
      [false,false,true],[false,true,false,true,true],[true,false,true]) := by decide +kernel

/-- Wrong bit order yields 4^11 mod23=1 on the same nonpalindromic word. -/
theorem wrong_order_counterexample : readout 5 [true,false,true,true] =
    (none,2,[true],[true,true,true,false,true],
      [false,false,true],[true,false,true,true],[true,false,true]) := by decide +kernel

/-- The caller's opaque saved data must survive even when the power is correct. -/
theorem corrupted_context_counterexample : readout 6 [true,false,true,true] =
    (none,2,[false,false,false,false,true],[true,true,true,false,true],
      [false,false,true],[true,false,true,true],[false,true,false,true]) := by decide +kernel

/-- Historical first coordinate: g2 raised to nonce3 modulo23 is8. Every
work port is empty, and the original exponent/context are retained. -/
theorem generator_full_control :
    tick^[clock 23 2] (start [false,true] [true,true] [true,true,true,false,true] [true,false,true]) =
      (⟨none,2,![[false,false,false,true],[],[],[],[],[],[true,true,true,false,true],
        [],[],[],[],[false,true],[],[true,true],[true,false,true]]⟩ : Config) := by
  have h := padded_run 23 2 [true,true] [true,false,true] (by decide) (by decide)
  exact h

/-- Historical second unmasked coordinate: pk4 raised to nonce3 gives18. -/
theorem key_full_control :
    tick^[clock 23 2] (start [false,false,true] [true,true] [true,true,true,false,true] [true,false,true]) =
      result [false,true,false,false,true] [false,false,true] [true,true]
        [true,true,true,false,true] [true,false,true] := by
  have h := padded_run 23 4 [true,true] [true,false,true] (by decide) (by decide)
  exact h

/-- Padded exponent digits are retained exactly despite the same numeric power. -/
theorem padded_full_control :
    tick^[clock 23 6] (start [false,false,true] [true,false,true,true,false,false]
      [true,true,true,false,true] [true,false,true]) =
      result [false,false,false,false,true] [false,false,true] [true,false,true,true,false,false]
        [true,true,true,false,true] [true,false,true] := by
  have h := padded_run 23 4 [true,false,true,true,false,false] [true,false,true] (by decide) (by decide)
  exact h

#print axioms generator_full_control
#print axioms key_full_control
#print axioms padded_full_control
#print axioms power_control
#print axioms empty_control
#print axioms zero_initialization_counterexample
#print axioms omitted_square_counterexample
#print axioms omitted_multiply_counterexample
#print axioms corrupted_exponent_counterexample
#print axioms wrong_order_counterexample
#print axioms corrupted_context_counterexample
end ExplainableCrypto.Helios.Computational.BinaryModPowerControls
