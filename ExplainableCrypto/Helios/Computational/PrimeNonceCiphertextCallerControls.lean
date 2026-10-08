import ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextCaller

namespace ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextCallerControls
open OracleComp OracleSpec BitOracleMachine PrimeNonceCiphertextCaller
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
set_option maxRecDepth 262144
set_option synthInstance.maxSize 512
private def handler : QueryImpl spec (StateT (List Bool × Nat × Nat) Id) := fun r state =>
  match r with
  | .coin => (state.1.headD false,(state.1.tail,state.2.1+1,state.2.2))
  | .hash w => (w,(state.1,state.2.1,state.2.2+1))
private def mutated (m : Nat) (l : Fin size) : Command 23 size 3 :=
  if m == 1 && l == pairLabel 0 then .compute
    (.load (fun _ => 2) (.goto (fun _ => routeLabel 0)))
  else if m == 2 && (l == routeLabel (PrimeNonceCiphertextMachine.copyLabel 0) ||
      l == routeLabel (PrimeNonceCiphertextMachine.copyLabel 1)) then
    match code l with
    | .compute s => .compute (TM2FiniteCoordinates.translate (Equiv.swap (20 : Fin 23) 21)
        (Equiv.refl _) (Equiv.refl _) s)
    | other => other
  else if m == 3 && l == 0 then .compute (.load (fun _ => 2) .halt)
  else if m == 4 && l == encryptLabel 4 then .compute
    (.load (fun _ => 0) (.goto (fun _ => encryptLabel 8)))
  else if m == 5 && l.val >= (pairLabel (PrimeNoncePairMachine.secondLabel 0)).val &&
      l.val < 165 then
    match code l with
    | .coin dest next => .compute (.push dest (fun _ => false) (.goto (fun _ => next)))
    | other => other
  else if m == 6 && l == 0 then
    match code l with
    | .compute s => .compute (.push 14 (fun _ => false) s)
    | other => other
  else if m == 7 && l == 0 then
    match code l with
    | .compute s => .compute (.push 20 (fun _ => false) s)
    | other => other
  else code l
private def lowHigh : List Bool := [false,false,false,false,true,true,true,true,true,false,true]
private def highLow : List Bool := [true,true,true,true,false,false,false,false,true,false,true]
private def readout (m : Nat) (vote : Bool) (tape : List Bool) :=
  let out := (simulateQ handler (Prod.fst <$> run (mutated m) 4000
    (start [false,true] [false,false,true] [true,true,true,false,true]
      [false,true,true,true,true,false,true,true,false,true] [true,false,true] vote))).run (tape,0,0)
  ((out.1.l,out.1.var.val,List.ofFn out.1.stk),out.2.1,out.2.2.1,out.2.2.2)
private def expected (mem : Nat) (alpha beta nonce first second context : List Bool)
    (vote : Bool) (remaining : List Bool) (coins : Nat) :
    (Option (Fin size) × Nat × List (List Bool)) × List Bool × Nat × Nat :=
  ((none,mem,[beta,[],[],[],[],[],[true,true,true,false,true],[],[],[],[],[],[],nonce,
    context,[false,false,true],[false,true],alpha,[vote],
    [false,true,true,true,true,false,true,true,false,true],first,second,[false,true,false,true]]),
    remaining,coins,0)

/-- Nonces1/6 from eight successive coins produce ciphertext(2,8) for true. -/
theorem low_high_true_control : readout 0 true lowHigh =
    expected 2 [false,true] [false,false,false,true] [true] [true,false,true]
      [true,true,true,false,false,true,true] [true,false,true] true [true,false,true] 8 := by
  decide +kernel
#print axioms low_high_true_control

/-- The same pair and coins give(2,4) for false, retaining both nonce prefixes. -/
theorem low_high_false_control : readout 0 false lowHigh =
    expected 2 [false,true] [false,false,true] [true] [true,false,true]
      [true,true,true,false,false,true,true] [true,false,true] false [true,false,true] 8 := by
  decide +kernel

/-- Reversing the extreme nonce words gives first6 and ciphertext(18,4). -/
theorem high_low_true_control : readout 0 true highLow =
    expected 2 [false,true,false,false,true] [false,false,true] [false,true,true]
      [true,true,true,false,false,true,true] [true,false,true] [true,false,true] true [true,false,true] 8 := by
  decide +kernel

/-- Omitting the second draw leaves first20 empty, first answer on21, and route rejection. -/
theorem omitted_second_counterexample : readout 1 true lowHigh =
    expected 1 [] [] [] [] [true,false,true] [true,false,true] true
      [true,true,true,true,true,false,true] 4 := by
  decide +kernel

/-- Selecting the second nonce changes the ciphertext to(18,4), with first prefix still1. -/
theorem wrong_nonce_counterexample : readout 2 true lowHigh =
    expected 2 [false,true,false,false,true] [false,false,true] [false,true,true]
      [true,false,true] [true,true,true,false,false,true,true] [true,false,true] true [true,false,true] 8 := by
  decide +kernel

/-- Halting after routing leaves both ciphertext coordinates empty despite success memory. -/
theorem omitted_encryption_counterexample : readout 3 true lowHigh =
    expected 2 [] [] [true] [true,false,true] [true,true,true,false,false,true,true]
      [true,false,true] true [true,false,true] 8 := by
  decide +kernel

/-- Omitting the vote multiplication gives beta4 for true instead of8. -/
theorem omitted_vote_counterexample : readout 4 true lowHigh =
    expected 2 [false,true] [false,false,true] [true] [true,false,true]
      [true,true,true,false,false,true,true] [true,false,true] true [true,false,true] 8 := by
  decide +kernel

/-- Replacing the second actual coin calls duplicates nonce1 and consumes only four coins. -/
theorem fixed_second_coins_counterexample : readout 5 true lowHigh =
    expected 2 [false,true] [false,false,false,true] [true] [true,false,true]
      [true,false,true] [true,false,true] true [true,true,true,true,true,false,true] 4 := by
  decide +kernel

/-- Correct ciphertext and nonce words do not excuse corrupted private context. -/
theorem corrupted_context_counterexample : readout 6 true lowHigh =
    expected 2 [false,true] [false,false,false,true] [true] [true,false,true]
      [true,true,true,false,false,true,true] [false,true,false,true] true [true,false,true] 8 := by
  decide +kernel

/-- Correct ciphertext does not excuse corruption of the already parsed first prefix. -/
theorem corrupted_first_prefix_counterexample : readout 7 true lowHigh =
    expected 2 [false,true] [false,false,false,true] [true] [false,true,false,true]
      [true,true,true,false,false,true,true] [true,false,true] true [true,false,true] 8 := by
  decide +kernel

#print axioms low_high_false_control
#print axioms high_low_true_control
#print axioms omitted_second_counterexample
#print axioms wrong_nonce_counterexample
#print axioms omitted_encryption_counterexample
#print axioms omitted_vote_counterexample
#print axioms fixed_second_coins_counterexample
#print axioms corrupted_context_counterexample
#print axioms corrupted_first_prefix_counterexample

end ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextCallerControls
