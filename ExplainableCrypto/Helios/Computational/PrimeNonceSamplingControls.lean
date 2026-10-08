import ExplainableCrypto.Helios.Computational.PrimeNonceSamplingSource

/-! Independently calculated complete nonce traces and actual-code defects. -/
namespace ExplainableCrypto.Helios.Computational.PrimeNonceSamplingControls
open OracleComp OracleSpec BitOracleMachine PrimeNonceMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
set_option maxRecDepth 32768

private def handler : QueryImpl spec (StateT (List Bool) Id) := fun r tape =>
  match r with
  | .coin => (tape.headD false,tape.tail)
  | .hash word => (word,tape)

def trace (slack q : Nat) (frame : Frame) (tape : List Bool) :=
  (simulateQ handler (Prod.fst <$> run sampleCode (sampleClock slack q)
    (sampleStart (SamplerOperands.input slack q []) frame))).run tape

private theorem trace_eq (slack q : Nat) (hq : 2 ≤ q) (frame : Frame) (tape : List Bool) :
    trace slack q frame tape =
      (simulateQ handler ((fun bits => sampleOutput
        (uniformNatEncode (bitsValue bits % (q-1)+1)) (q-1).bits frame) <$>
        CoinWordLoader.word (sampleWidth slack q))).run tape := by
  obtain ⟨c,_,he⟩ := sample_source slack q hq frame
  unfold trace
  rw [he]
  simp only [Functor.map_map]

private def saved : Frame := ![[true],[false,true],[false]]

/-- At q=2, exactly one coin is consumed and the only nonce is one. -/
theorem two_control : trace 0 2 saved [false,true,false] =
    (sampleOutput [true,false,true] [true] saved,[true,false]) := by
  rw [trace_eq 0 2 (by decide)]
  rfl

/-- Three one-coins give index 7 mod 4, hence the maximal nonce four at q=5. -/
theorem upper_control : trace 0 5 saved [true,true,true,false] =
    (sampleOutput [true,true,true,false,false,false,true] [false,false,true] saved,[false]) := by
  rw [trace_eq 0 5 (by decide)]
  rfl

/-- The saved words survive the complete public-input sampler and successor. -/
theorem frame_control :
    (trace 0 5 saved [true,true,true,false]).1.stk 9 = [false,true] := by
  rw [upper_control]
  rfl

/-- The least field cannot return the encoded zero index as its nonce. -/
theorem zero_not_returned : (trace 0 2 saved [false,true,false]).1.stk 5 ≠ [false] := by
  rw [two_control]
  decide +kernel

private def mutated (m : Nat) (l : Fin 71) : Command 11 71 3 :=
  if m == 1 && l == operandLabel 8 then .compute
    (.load (fun _ => 2) (.goto (fun _ => operandLabel 12)))
  else if m == 2 && l == tailLabel 28 then .compute .halt
  else if m == 3 && l == tailLabel (responseLabel 25) then .compute
    (.push 8 (fun _ => false) .halt)
  else if m == 4 && l == operandLabel 12 then
    match sampleCode l with
    | .compute s => .compute (.push 2 (fun _ => true) s)
    | other => other
  else sampleCode l

private def mutantReadout (m : Nat) :=
  let out := (simulateQ handler (Prod.fst <$> run (mutated m) 200
    (sampleStart (SamplerOperands.input 0 2 []) (fun _ => [])))).run [false,true,false,true]
  (out.1.stk 1,out.1.stk 5,out.1.stk 8,out.2)

/-- Bypassing predecessor retains modulus two and consumes an extra coin. -/
theorem omitted_decrement_counterexample : mutantReadout 1 =
    ([false,true],[true,false,true],[],[false,true]) := by decide +kernel

/-- Bypassing successor returns the forbidden zero nonce. -/
theorem omitted_successor_counterexample : mutantReadout 2 =
    ([true],[false],[],[true,false,true]) := by decide +kernel

/-- Writing into the saved frame is observable even when the nonce is correct. -/
theorem corrupted_frame_counterexample : mutantReadout 3 =
    ([true],[true,false,true],[false],[true,false,true]) := by decide +kernel

/-- Stale width can return the right nonce while consuming the wrong coin tree. -/
theorem stale_width_counterexample : mutantReadout 4 =
    ([true],[true,false,true],[],[false,true]) := by decide +kernel

#print axioms two_control
#print axioms upper_control
#print axioms frame_control
#print axioms zero_not_returned
#print axioms omitted_decrement_counterexample
#print axioms omitted_successor_counterexample
#print axioms corrupted_frame_counterexample
#print axioms stale_width_counterexample
end ExplainableCrypto.Helios.Computational.PrimeNonceSamplingControls
