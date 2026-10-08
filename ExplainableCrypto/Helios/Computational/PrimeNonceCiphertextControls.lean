import ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextMachine

/-! Independent literal controls: the q5 pair's first and second nonces differ. -/
namespace ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextControls
open PrimeNonceCiphertextMachine
set_option maxRecDepth 32768
set_option synthInstance.maxSize 512

private def mutated (m : Nat) (l : Fin 7) :=
  if m == 1 && (l == copyLabel 0 || l == copyLabel 1) then
    TM2FiniteCoordinates.translate (Equiv.swap (20 : Fin 23) 21)
      (Equiv.refl _) (Equiv.refl _) (program l)
  else if m == 2 && l == 0 then
    .load (fun _ => 0) (.goto (fun _ => parseLabel 0))
  else if m == 3 && l == parseLabel 0 then .load (fun _ => 2) .halt
  else if m == 4 && l == 1 then
    .branch (fun v => v == 2) (.load (fun _ => 2) .halt) (.load (fun _ => 1) .halt)
  else if m == 5 && l == 1 then .push 20 (fun _ => false) (program l)
  else if m == 6 && l == 1 then .push 14 (fun _ => false) (program l)
  else program l

private def readout (m : Nat) (first second : List Bool) :=
  let out := (TM2ReturnLink.tick (mutated m))^[64]
    (start [false,true,true,true,false,true,false,true] first second [false,false,true]
      [true,false,true,true,false] [true,true,true,false,true] [false,true] [false,false,true] true)
  (out.l,out.var.val,List.ofFn out.stk)

/-- Independent literal complete port map; does not invoke the machine result constructor. -/
private def expected (mem : Nat) (nonce first second pending context : List Bool) :
    Option (Fin 7) × Nat × List (List Bool) :=
  (none,mem,[[],[],[],[],[],[],[true,true,true,false,true],pending,[],[],[],[],[],nonce,
    context,[false,false,true],[false,true],[],[true],
    [false,true,true,true,false,true,false,true],first,second,[false,false,true]])

/-- The actual q5 pair can return first1 and second4; the route selects first1. -/
theorem low_high_control : readout 0 [true,false,true] [true,true,true,false,false,false,true] =
    expected 2 [true] [true,false,true] [true,true,true,false,false,false,true] []
      [true,false,true,true,false] := by decide +kernel

/-- Reversing the pair's two distinct outcomes routes4 and retains second1. -/
theorem high_low_control : readout 0 [true,true,true,false,false,false,true] [true,false,true] =
    expected 2 [false,false,true] [true,true,true,false,false,false,true] [true,false,true] []
      [true,false,true,true,false] := by decide +kernel

/-- Copying the second prefix selects4 instead of first1 despite preserving both prefixes. -/
theorem wrong_nonce_counterexample : readout 1 [true,false,true] [true,true,true,false,false,false,true] =
    expected 2 [false,false,true] [true,false,true] [true,true,true,false,false,false,true] []
      [true,false,true,true,false] := by decide +kernel

/-- Skipping the actual copy makes the parser reject its empty input. -/
theorem omitted_copy_counterexample : readout 2 [true,false,true] [true,true,true,false,false,false,true] =
    expected 1 [] [true,false,true] [true,true,true,false,false,false,true] []
      [true,false,true,true,false] := by decide +kernel

/-- Skipping parsing falsely signals success with a copied prefix still on input7. -/
theorem omitted_parser_counterexample : readout 3 [true,false,true] [true,true,true,false,false,false,true] =
    expected 2 [] [true,false,true] [true,true,true,false,false,false,true] [true,false,true]
      [true,false,true,true,false] := by decide +kernel

/-- Successful prefix decoding does not justify accepting a remaining suffix. -/
theorem unchecked_suffix_counterexample : readout 4 [true,false,true,false] [true,true,true,false,false,false,true] =
    expected 2 [true] [true,false,true,false] [true,true,true,false,false,false,true] [false]
      [true,false,true,true,false] := by decide +kernel

/-- This particular suffix input rejects and retains its saved first prefix.
No assertion of universal rejected-work cleanup is made. -/
theorem suffix_rejection_control :
    let out := readout 0 [true,false,true,false] [true,true,true,false,false,false,true]
    out.1 = none ∧ out.2.1 = 1 ∧ out.2.2[20]? = some [true,false,true,false] := by
  decide +kernel

/-- Correct routed digits do not excuse corruption of the saved scalar prefix. -/
theorem corrupted_saved_prefix_counterexample : readout 5 [true,false,true] [true,true,true,false,false,false,true] =
    expected 2 [true] [false,true,false,true] [true,true,true,false,false,false,true] []
      [true,false,true,true,false] := by decide +kernel

/-- Correct routed digits do not excuse corruption of private caller data. -/
theorem corrupted_context_counterexample : readout 6 [true,false,true] [true,true,true,false,false,false,true] =
    expected 2 [true] [true,false,true] [true,true,true,false,false,false,true] []
      [false,true,false,true,true,false] := by decide +kernel

#print axioms low_high_control
#print axioms high_low_control
#print axioms wrong_nonce_counterexample
#print axioms omitted_copy_counterexample
#print axioms omitted_parser_counterexample
#print axioms unchecked_suffix_counterexample
#print axioms suffix_rejection_control
#print axioms corrupted_saved_prefix_counterexample
#print axioms corrupted_context_counterexample
end ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextControls
