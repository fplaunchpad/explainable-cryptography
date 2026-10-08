import ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachineRun

/-! Literal full-state numeric regressions from the independent adjusted-beta
gate. Full arithmetic uses the checked padded run; mutation controls reduce
actual one-step instructions at the power-return boundary in the kernel. -/
namespace ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachineControls
open Turing.TM2 PrimeAdjustedBetaMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
private def observe (cfg : Config) := (cfg.l.map Fin.val,cfg.var.val,List.ofFn cfg.stk)

private def smallInput : Fin 39 → List Bool :=
  ![[false,true],
    [true,false,true],
    [false,true],
    [true],
    [],
    [],
    [true,true],
    [false],
    [],
    [],
    [false],
    [true,false,true],
    [true,false,true],
    [true],
    [true,true,true,false,true,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,false,true,true,false,true,true,false,false,true,true,false,true,true,true,true,false,true,true,true,false,true],
    [true],
    [false,true],
    [false,true],
    [true],
    [false,true,true,false,false,true],
    [true,false,true],
    [true,false,true],
    [true],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [false,true]]
private def smallFrame : Fin 20 → List Bool :=
  ![[true,false,true],
    [false,true],
    [true],
    [],
    [],
    [false],
    [],
    [],
    [false],
    [true,false,true],
    [true,false,true],
    [true],
    [true,true,true,false,true,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,false,true,true,false,true,true,false,false,true,true,false,true,true,true,true,false,true,true,true,false,true],
    [true],
    [false,true],
    [true],
    [false,true,true,false,false,true],
    [true,false,true],
    [true,false,true],
    [false,true]]
private def smallExpected : List (List Bool) :=
  [[false,true],
    [true,false,true],
    [false,true],
    [true],
    [],
    [],
    [true,true],
    [false],
    [],
    [],
    [false],
    [true,false,true],
    [true,false,true],
    [true],
    [true,true,true,false,true,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,false,true,true,false,true,true,false,false,true,true,false,true,true,true,true,false,true,true,true,false,true],
    [true],
    [false,true],
    [false,true],
    [true],
    [false,true,true,false,false,true],
    [true,false,true],
    [true,false,true],
    [true],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [false,true],
    [true]]

/-- Independent integer calculation: 2 * (2^(2-1) mod 3) mod 3 = 1.
The complete saved d-prefix, both commitment coordinates and context remain. -/
theorem small_full_state :
    observe (tick^[clock 3 2] (start smallInput)) = (none,2,smallExpected) := by
  have h := padded_run 3 2 2 2 (by decide) (by decide) (by decide) smallFrame
  have hs : inputWords 3 2 2 2 smallFrame = smallInput := by
    funext k; fin_cases k <;> rfl
  rw [hs] at h
  exact congrArg observe h

private def largeInput : Fin 39 → List Bool :=
  ![[true],
    [true,true,false,false,true],
    [true,true],
    [true],
    [],
    [],
    [true,true,true],
    [true,true,false,false,true],
    [],
    [],
    [false],
    [true,false,true],
    [true,false,true],
    [true],
    [true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,false,true],
    [false,false,true],
    [false,true],
    [false,true],
    [true],
    [false,true,true,false,true,true],
    [true,false,true],
    [true,true,false,false,true],
    [false,true],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [false,false,true]]
private def largeFrame : Fin 20 → List Bool :=
  ![[true,true,false,false,true],
    [true,true],
    [true],
    [],
    [],
    [true,true,false,false,true],
    [],
    [],
    [false],
    [true,false,true],
    [true,false,true],
    [true],
    [true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,false,true],
    [false,false,true],
    [false,true],
    [true],
    [false,true,true,false,true,true],
    [true,false,true],
    [true,true,false,false,true],
    [false,false,true]]
private def largeExpected : List (List Bool) :=
  [[true],
    [true,true,false,false,true],
    [true,true],
    [true],
    [],
    [],
    [true,true,true],
    [true,true,false,false,true],
    [],
    [],
    [false],
    [true,false,true],
    [true,false,true],
    [true],
    [true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,false,true],
    [false,false,true],
    [false,true],
    [false,true],
    [true],
    [false,true,true,false,true,true],
    [true,false,true],
    [true,true,false,false,true],
    [false,true],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [false,false,true],
    [false,false,true]]

/-- Independent integer calculation: 1 * (2^(3-1) mod 7) mod 7 = 4.
The complete saved d-prefix, both commitment coordinates and context remain. -/
theorem large_full_state :
    observe (tick^[clock 7 3] (start largeInput)) = (none,2,largeExpected) := by
  have h := padded_run 7 3 2 1 (by decide) (by decide) (by decide) largeFrame
  have hs : inputWords 7 3 2 1 largeFrame = largeInput := by
    funext k; fin_cases k <;> rfl
  rw [hs] at h
  exact congrArg observe h

/-- A concrete power-return boundary; its inverse is 2^2 mod7=4. These
controls concern the actual next instruction, not a second whole-run campaign. -/
private def boundary : Config :=
  ⟨some 1,2,Function.update (initialWords largeInput) 23 [false,false,true]⟩
private def boundaryWords := List.ofFn boundary.stk
private def mutant (m : Nat) (l : Fin size) :=
  if m == 0 && l == 1 then .load (fun _ => 2) .halt
  else if m == 1 && l == 1 then .pop 1 (fun v _ => v) (program l)
  else program l

/-- The original guard enters the product with every saved word intact. -/
theorem original_product_entry :
    observe (tick boundary) = (some 278,0,boundaryWords) := by decide +kernel

/-- The actual gate's skipped-product mutation halts with no gamma output. -/
theorem skipped_product_boundary :
    observe (TM2ReturnLink.tick (mutant 0) boundary) = (none,2,boundaryWords) := by decide +kernel

theorem skipped_product_is_detected :
    observe (TM2ReturnLink.tick (mutant 0) boundary) ≠ (none,2,largeExpected) := by
  rw [skipped_product_boundary]
  decide +kernel

/-- A new local mutation removes one bit from the retained d-prefix before
entering the same product. This is a boundary control, not a native gate case. -/
theorem lost_difference_prefix_boundary :
    observe (TM2ReturnLink.tick (mutant 1) boundary) =
      (some 278,0,boundaryWords.set 1 [true,false,false,true]) := by decide +kernel

theorem lost_difference_prefix_is_detected :
    observe (TM2ReturnLink.tick (mutant 1) boundary) ≠ observe (tick boundary) := by
  rw [lost_difference_prefix_boundary,original_product_entry]
  decide +kernel

#print axioms small_full_state
#print axioms large_full_state
#print axioms original_product_entry
#print axioms skipped_product_boundary
#print axioms skipped_product_is_detected
#print axioms lost_difference_prefix_boundary
#print axioms lost_difference_prefix_is_detected
end ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachineControls
