import ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCallerSource

namespace ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCallerControls
open PrimeHonestTranscriptCaller OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option synthInstance.maxSize 512

/-- The whole typed source-result configuration enters the transcript controller
without reconstruction assumptions or an extra source of initialized words. -/
theorem typed_prefix_entry {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (rs : ZMod q × ZMod q) :
    BitOracleReturnLink.embed cipherLabel (some (drawLabel (PrimeTranscriptDraws.sampleLabel 0 0)))
      (PrimeHonestCiphertextMachine.sourceResult slack g pk vote saved rs) =
    BitOracleReturnLink.embed drawLabel none
      (continuation (PrimeHonestCiphertextMachine.sourceResult slack g pk vote saved rs) vote) := rfl

private def raw : List Bool := [true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,false,true,true,true,true,true,true,false,true,true,false,true,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,false,true,true,false,true,true,false,false,true,true,false,true,true,true,true,false,true,true,true,false,true]
private def reached : Config := ⟨some 753,2,![[false,false,true],[],[],[],[],[],[true,false,true],[],[],[],[],[],[],[true],raw,[true],[false,false,true],[false,false,true],[true],[false,true,true,false,false,true],[true,false,true],[true,false,true],[true]]⟩

/-- The independently encoded p5/q2/g4/pk1 raw fixture gives the complete
reached entry frame. Both chronological nonces equal one in this q2 boundary. -/
theorem literal_prefix_entry :
    BitOracleReturnLink.embed cipherLabel (some (drawLabel (PrimeTranscriptDraws.sampleLabel 0 0)))
      (prefixResult 0 5 2 4 1 raw true [false] [true]) = reached := by
  rfl

private def handler : QueryImpl spec (StateT (List Bool × Nat × Nat) Id) := fun r state =>
  match r with
  | .coin => (state.1.headD false,(state.1.tail,state.2.1+1,state.2.2))
  | .hash w => (w,(state.1,state.2.1,state.2.2+1))
/-- Exact entry mutations from the independent raw-input campaign. -/
private def mutated (m : Nat) (l : Fin size) : Command 23 size 3 :=
  if m == 1 && l == drawLabel (PrimeTranscriptDraws.sampleLabel 0 0) then
    .compute (.load (fun _ => 2) .halt)
  else if m == 2 && l == drawLabel (PrimeTranscriptDraws.sampleLabel 0 0) then
    match code l with
    | .compute t => .compute (.push 14 (fun _ => false) t)
    | c => c
  else code l
private def entryView (m : Nat) :=
  let out := (simulateQ handler (step (mutated m) reached)).run ([false,false,true],0,0)
  ((out.1.1.l.map Fin.val,out.1.1.var.val,List.ofFn out.1.1.stk),out.2)

/-- The actual entry guard resets memory and enters the sampler while retaining
the complete prior state. No coin or hash is consumed by this guard. -/
theorem actual_entry_preserves_full_frame : entryView 0 =
    ((some 754,0,[[false,false,true],[],[],[],[],[],[true,false,true],[],[],[],[],[],[],[true],raw,[true],[false,false,true],[false,false,true],[true],[false,true,true,false,false,true],[true,false,true],[true,false,true],[true]]),([false,false,true],0,0)) := by decide +kernel

/-- Skipping all draws halts on the unchanged unsampled frame. This is the
entry boundary of the whole-run mutation, not a new whole-run trace claim. -/
theorem skipped_all_draws_boundary : entryView 1 =
    ((none,2,[[false,false,true],[],[],[],[],[],[true,false,true],[],[],[],[],[],[],[true],raw,[true],[false,false,true],[false,false,true],[true],[false,true,true,false,false,true],[true,false,true],[true,false,true],[true]]),([false,false,true],0,0)) ∧ entryView 1 ≠ entryView 0 := by decide +kernel

/-- The context mutation adds a bit to the exact original raw input at14;
the other22ports, next label and query observations agree with the original. -/
theorem corrupted_context_boundary : entryView 2 =
    ((some 754,0,[[false,false,true],[],[],[],[],[],[true,false,true],[],[],[],[],[],[],[true],(false::raw),[true],[false,false,true],[false,false,true],[true],[false,true,true,false,false,true],[true,false,true],[true,false,true],[true]]),([false,false,true],0,0)) ∧ entryView 2 ≠ entryView 0 := by decide +kernel

#print axioms typed_prefix_entry
#print axioms literal_prefix_entry
#print axioms actual_entry_preserves_full_frame
#print axioms skipped_all_draws_boundary
#print axioms corrupted_context_boundary
end ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCallerControls
