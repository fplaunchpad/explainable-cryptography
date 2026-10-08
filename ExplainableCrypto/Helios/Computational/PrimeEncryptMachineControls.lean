import ExplainableCrypto.Helios.Computational.PrimeEncryptMachine

/-! Independently derived literal full-state encryption controls and actual-code mutants. -/
namespace ExplainableCrypto.Helios.Computational.PrimeEncryptMachineControls
open PrimeEncryptMachine
set_option maxRecDepth 262144
set_option synthInstance.maxSize 512

private def mutated (m : Nat) (l : Fin 490) :=
  if m == 1 && l == powerLabel 0 (BinaryModPower.copyLabel 0 0) then
    .load (fun _ => 2) (.goto (fun _ => 0))
  else if m == 2 && l == powerLabel 1 (BinaryModPower.copyLabel 0 0) then
    .load (fun _ => 2) (.goto (fun _ => 3))
  else if m == 3 && (l == copyLabel 2 0 || l == copyLabel 2 1) then
    TM2FiniteCoordinates.translate (Equiv.swap (15 : Fin 19) 16) (Equiv.refl _) (Equiv.refl _) (program l)
  else if m == 4 && l == 4 then enter 8
  else if m == 5 && l == 3 then .push 17 (fun _ => false) (control 3)
  else if m == 6 && l == 3 then .push 13 (fun _ => false) (control 3)
  else if m == 7 && l == 3 then .push 14 (fun _ => false) (control 3)
  else program l

private def readout (m : Nat) (vote : Bool) :=
  let out := (TM2ReturnLink.tick (mutated m))^[2300]
    (start [false,true] [false,false,true] [true,true]
      [true,true,true,false,true] [true,false,true] vote)
  (out.l,out.var.val,List.ofFn out.stk)

/-- The literal 19-port expectation is independent of the controller's result constructor. -/
private def expected (alpha beta nonce context : List Bool) (vote : Bool) :
    Option (Fin 490) × Nat × List (List Bool) :=
  (none,2,[beta,[],[],[],[],[],[true,true,true,false,true],[],[],[],[],[],[],
    nonce,context,[false,false,true],[false,true],alpha,[vote]])

/-- True vote: alpha=2^3 mod23=8; beta=(4^3 mod23)*2 mod23=13. -/
theorem true_vote_control : readout 0 true =
    expected [false,false,false,true] [true,false,true,true] [true,true] [true,false,true] true := by
  decide +kernel

/-- False vote: alpha=8 and beta=4^3 mod23=18, with all retained and work ports checked. -/
theorem false_vote_control : readout 0 false =
    expected [false,false,false,true] [false,true,false,false,true] [true,true] [true,false,true] false := by
  decide +kernel

/-- Omitting the first power leaves the first coordinate empty (zero). -/
theorem omitted_first_power_counterexample : readout 1 true =
    expected [] [true,false,true,true] [true,true] [true,false,true] true := by
  decide +kernel

/-- Omitting the second power produces zero as the second coordinate. -/
theorem omitted_second_power_counterexample : readout 2 true =
    expected [false,false,false,true] [] [true,true] [true,false,true] true := by
  decide +kernel

/-- Replacing the public key by the generator gives beta=2^3*2 mod23=16. -/
theorem reused_generator_counterexample : readout 3 true =
    expected [false,false,false,true] [false,false,false,false,true] [true,true] [true,false,true] true := by
  decide +kernel

/-- Omitting the true-vote product incorrectly leaves beta=18. -/
theorem omitted_vote_product_counterexample : readout 4 true =
    expected [false,false,false,true] [false,true,false,false,true] [true,true] [true,false,true] true := by
  decide +kernel

/-- Prefixing a zero bit doubles the saved first coordinate to sixteen. -/
theorem corrupted_alpha_counterexample : readout 5 true =
    expected [false,false,false,false,true] [true,false,true,true] [true,true] [true,false,true] true := by
  decide +kernel

/-- A correct ciphertext does not permit corruption of the retained nonce word. -/
theorem corrupted_nonce_counterexample : readout 6 true =
    expected [false,false,false,true] [true,false,true,true] [false,true,true] [true,false,true] true := by
  decide +kernel

/-- A correct ciphertext does not permit corruption of opaque caller data. -/
theorem corrupted_context_counterexample : readout 7 true =
    expected [false,false,false,true] [true,false,true,true] [true,true] [false,true,false,true] true := by
  decide +kernel

#print axioms true_vote_control
#print axioms false_vote_control
#print axioms omitted_first_power_counterexample
#print axioms omitted_second_power_counterexample
#print axioms reused_generator_counterexample
#print axioms omitted_vote_product_counterexample
#print axioms corrupted_alpha_counterexample
#print axioms corrupted_nonce_counterexample
#print axioms corrupted_context_counterexample
end ExplainableCrypto.Helios.Computational.PrimeEncryptMachineControls
