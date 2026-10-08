import ExplainableCrypto.Helios.Computational.PrimeTranscriptDrawsRun

namespace ExplainableCrypto.Helios.Computational.PrimeTranscriptDrawsControls
open PrimeTranscriptDraws OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option synthInstance.maxSize 512
private def handler : QueryImpl spec (StateT (List Bool × Nat × Nat) Id) := fun r state =>
  match r with
  | .coin => (state.1.headD false,(state.1.tail,state.2.1+1,state.2.2))
  | .hash w => (w,(state.1,state.2.1,state.2.2+1))
private def context : List Bool := [true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,false,true,true,true,true,true,true,false,true,true,false,true,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,false,true,true,false,true,true,false,false,true,true,false,true,true,true,true,false,true,true,true,false,true]
private def observe (oa : OracleComp spec (Config × Nat)) (tape : List Bool) :=
  let out := (simulateQ handler (Prod.fst <$> oa)).run (tape,0,0)
  ((out.1.l,out.1.var.val,List.ofFn out.1.stk),out.2)

/-- The independently computed q=2 fixture has four zero scalars, consumes
exactly eight fresh coins, makes no hash query and preserves the full frame.
The general execution equation reduces the kernel check to the four word draws. -/
theorem four_zero_scalars_full_state :
    observe (BitOracleMachine.run code (clock 0 2)
      (start [false,false,true] [false,false,true] [true] (SamplerOperands.input 0 2 [])
        [true,false,true] [true,false,true] [true] context [true,false,true]
        [false,false,true] [true] true))
      [false,false,false,false,false,false,false,false,true,false,true] =
    ((none,2,[[false,false,true],[],[false,true],[],[],[],[true,false,true],[false],[],[],[false],[false],[false],[true],context,[true],[false,false,true],[false,false,true],[true],[false,true,true,false,false,true],[true,false,true],[true,false,true],[true]]),([true,false,true],8,0)) := by
  obtain ⟨charge,_,he⟩ := charged 0 2 (by decide)
    [false,false,true] [false,false,true] [true] [true,false,true] [true,false,true] [true]
    context [true,false,true] [false,false,true] [true] true
  unfold observe
  rw [he]
  simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
  decide +kernel

/-- These are the same skipped-draw, wrong-save-phase and omitted-clear
instruction mutations used in the independent eight-case campaign. -/
private def mutated (m : Nat) (l : Fin size) : Command 23 size 3 :=
  if m == 1 && l == sampleLabel 1 0 then
    .compute (.load (fun _ => 2) (.goto (fun _ => saveLabel 1 0)))
  else if m == 3 && l.val >= 199 && l.val < 206 then
    BitOracleReturnLink.command (saveLabel 1) (some (saveReturn 1))
      (TranscriptScalarSave.code 0 ⟨(l.val-199)%7,by omega⟩)
  else if m == 4 && (l == saveLabel 0 1 || l == saveLabel 1 1 || l == saveLabel 2 1) then
    .compute (.goto (fun _ => if l == saveLabel 0 1 then saveLabel 0 2
      else if l == saveLabel 1 1 then saveLabel 1 2 else saveLabel 2 2))
  else code l
private def boundary (label : Fin size) (words : Fin 23 → List Bool) : Config :=
  ⟨some label,2,words⟩
private def stepView (m : Nat) (cfg : Config) :=
  let out := (simulateQ handler (step (mutated m) cfg)).run ([true,false,true],0,0)
  ((out.1.1.l.map Fin.val,out.1.1.var.val,
    out.1.1.stk 2,out.1.1.stk 7,out.1.1.stk 10,out.1.1.stk 11),out.2)

/-- The actual second-draw guard enters its sampler; the skipped-draw mutant
jumps directly to saving, with the previous c still present. -/
theorem skipped_second_draw_boundary :
    stepView 0 (boundary (sampleLabel 1 0) (Function.update (fun _ => []) 10 [false])) =
      ((some 49,0,[],[],[false],[]),([true,false,true],0,0)) ∧
    stepView 1 (boundary (sampleLabel 1 0) (Function.update (fun _ => []) 10 [false])) =
      ((some 199,2,[],[],[false],[]),([true,false,true],0,0)) := by decide +kernel

/-- The correct phase clears its empty e destination and advances. The wrong
save-phase mutation instead removes the already saved c bit and repeats. -/
theorem wrong_save_destination_boundary :
    stepView 0 (boundary (saveLabel 1 2) (Function.update (fun _ => []) 10 [false])) =
      ((some 202,0,[],[],[false],[]),([true,false,true],0,0)) ∧
    stepView 3 (boundary (saveLabel 1 2) (Function.update (fun _ => []) 10 [false])) =
      ((some 201,1,[],[],[],[]),([true,false,true],0,0)) := by decide +kernel

/-- The actual clear removes one modulus bit and stays in its clearing loop.
The mutant enters scalar transfer with both modulus bits still resident. This
is a bounded boundary witness, not an eventual-nontermination theorem. -/
theorem omitted_modulus_clear_boundary :
    stepView 0 (boundary (saveLabel 0 1) (Function.update (fun _ => []) 2 [false,true])) =
      ((some 193,1,[true],[],[],[]),([true,false,true],0,0)) ∧
    stepView 4 (boundary (saveLabel 0 1) (Function.update (fun _ => []) 2 [false,true])) =
      ((some 194,2,[false,true],[],[],[]),([true,false,true],0,0)) := by decide +kernel

#print axioms four_zero_scalars_full_state
#print axioms skipped_second_draw_boundary
#print axioms wrong_save_destination_boundary
#print axioms omitted_modulus_clear_boundary
end ExplainableCrypto.Helios.Computational.PrimeTranscriptDrawsControls
