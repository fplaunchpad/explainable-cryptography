import ExplainableCrypto.Helios.Computational.PrimeHonestCiphertextMachine

namespace ExplainableCrypto.Helios.Computational.PrimeHonestCiphertextControls
open PrimeHonestCiphertextMachine OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
set_option maxRecDepth 262144
set_option maxHeartbeats 0
set_option synthInstance.maxSize 512
private def handler : QueryImpl spec (StateT (List Bool × Nat × Nat) Id) := fun r state =>
  match r with
  | .coin => (state.1.headD false,(state.1.tail,state.2.1+1,state.2.2))
  | .hash w => (w,(state.1,state.2.1,state.2.2+1))
private def mutated (m : Nat) (l : Fin size) : Command 23 size 3 :=
  if m == 1 && l == inputLabel (PrimeHonestInputMachine.copyLabel 0) then
    .compute (.load (fun _ => 0) (.goto (fun _ => 0)))
  else if m == 2 && l == 0 then
    .compute (.load (fun _ => 0) (.goto (fun _ => callerLabel callerEntry)))
  else if m == 3 && l == 0 then
    .compute (.load (fun _ => 0) (.goto (fun _ => callerLabel (PrimeNonceCiphertextCaller.routeLabel 0))))
  else if m == 4 && l == 0 then
    match code l with
    | .compute s => .compute (.push 14 (fun _ => false) s)
    | c => c
  else if m == 5 && l == 0 then
    match code l with
    | .compute s => .compute (.push 16 (fun _ => false) s)
    | c => c
  else code l
private def execute (m : Nat) : Nat → Config → (List Bool × Nat × Nat) → Nat → Nat →
    Config × (List Bool × Nat × Nat) × Nat × Nat
  | 0,cfg,state,used,charge => (cfg,state,used,charge)
  | n+1,cfg,state,used,charge => match cfg.l with
    | none => (cfg,state,used,charge)
    | some _ =>
      let out := (simulateQ handler (step (mutated m) cfg)).run state
      execute m n out.1.1 out.2 (used+1) (charge+out.1.2)
private def observed (m fuel : Nat) (raw tape : List Bool) :=
  let out := execute m fuel (start raw) (tape,0,0) 0 0
  ((out.1.l,out.1.var.val,List.ofFn out.1.stk),out.2.1.1,out.2.1.2.1,out.2.1.2.2,out.2.2.1,out.2.2.2)
private def agrees (m fuel bound : Nat) (raw tape : List Bool) (mem : Nat)
    (ws : List (List Bool)) (remaining : List Bool) (coins : Nat) : Prop :=
  let out := observed m fuel raw tape
  out.1 = (none,mem,ws) ∧ out.2.1 = remaining ∧ out.2.2.1 = coins ∧
    out.2.2.2.1 = 0 ∧ out.2.2.2.2.1 ≤ fuel ∧ out.2.2.2.2.2 ≤ bound

theorem skipped_initializer_counterexample : agrees 1 165603 5460484 [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true] [false,false,false,false,true,true,true,true,true,false,true] 1 [[],[],[],[],[],[],[],[true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]] [false,false,false,false,true,true,true,true,true,false,true] 0 := by
  dsimp only [agrees]
  decide +kernel
#print axioms skipped_initializer_counterexample

theorem failed_initializer_guard_control : agrees 0 148983 4763041 [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true] [false,false,false,false,true,true,true,true,true,false,true] 1 [[],[],[],[],[],[],[true,true,true,false,true],[true],[],[],[],[],[],[],[true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true],[false,false,true],[false,true],[],[true],[false,true,true,true,true,false,true,true,false,true],[],[],[]] [false,false,false,false,true,true,true,true,true,false,true] 0 := by
  dsimp only [agrees]
  decide +kernel
#print axioms failed_initializer_guard_control

theorem bypassed_failure_guard_counterexample : agrees 2 148983 4912024 [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true] [false,false,false,false,true,true,true,true,true,false,true] 1 [[],[],[],[],[],[],[true,true,true,false,true],[true],[],[],[],[],[],[true],[true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true],[false,false,true],[false,true],[],[true],[false,true,true,true,true,false,true,true,false,true],[true,false,true],[true,true,true,false,false,true,true],[false,true,false,true]] [true,false,true] 8 := by
  dsimp only [agrees]
  decide +kernel
#print axioms bypassed_failure_guard_counterexample

theorem wrong_caller_entry_counterexample : agrees 3 165603 5460484 [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true] [false,false,false,false,true,true,true,true,true,false,true] 1 [[],[],[],[],[],[],[true,true,true,false,true],[],[],[],[],[],[],[],[true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[false,true],[],[true],[false,true,true,true,true,false,true,true,false,true],[],[],[]] [false,false,false,false,true,true,true,true,true,false,true] 0 := by
  dsimp only [agrees]
  decide +kernel
#print axioms wrong_caller_entry_counterexample

theorem corrupted_context_counterexample : agrees 4 165603 5460484 [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true] [false,false,false,false,true,true,true,true,true,false,true] 2 [[false,false,false,true],[],[],[],[],[],[true,true,true,false,true],[],[],[],[],[],[],[true],[false,true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[false,true],[false,true],[true],[false,true,true,true,true,false,true,true,false,true],[true,false,true],[true,true,true,false,false,true,true],[false,true,false,true]] [true,false,true] 8 := by
  dsimp only [agrees]
  decide +kernel
#print axioms corrupted_context_counterexample

theorem overwritten_generator_counterexample : agrees 5 165603 5460484 [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true] [false,false,false,false,true,true,true,true,true,false,true] 2 [[false,false,false,false,true],[],[],[],[],[],[true,true,true,false,true],[],[],[],[],[],[],[true],[true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[false,false,true],[false,false,true],[true],[false,true,true,true,true,false,true,true,false,true],[true,false,true],[true,true,true,false,false,true,true],[false,true,false,true]] [true,false,true] 8 := by
  dsimp only [agrees]
  decide +kernel
#print axioms overwritten_generator_counterexample

theorem canonical_0 : agrees 0 165603 5294881 [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,true,false,true,true,true,false,true] [false,false,false,false,true,true,true,true,true,false,true] 2 [[false,false,true],[],[],[],[],[],[true,true,true,false,true],[],[],[],[],[],[],[true],[true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,true,false,true,true,true,false,true],[false,false,true],[false,true],[false,true],[false],[false,true,true,true,true,false,true,true,false,true],[true,false,true],[true,true,true,false,false,true,true],[false,true,false,true]] [true,false,true] 8 := by
  dsimp only [agrees]
  decide +kernel
#print axioms canonical_0

theorem canonical_1 : agrees 0 165603 5294881 [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,true,false,true,true,true,false,true] [true,true,true,true,false,false,false,false,true,false,true] 2 [[false,true],[],[],[],[],[],[true,true,true,false,true],[],[],[],[],[],[],[false,true,true],[true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,true,false,true,true,true,false,true],[false,false,true],[false,true],[false,true,false,false,true],[false],[false,true,true,true,true,false,true,true,false,true],[true,true,true,false,false,true,true],[true,false,true],[false,true,false,true]] [true,false,true] 8 := by
  dsimp only [agrees]
  decide +kernel
#print axioms canonical_1

theorem canonical_2 : agrees 0 165603 5294881 [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true] [false,false,false,false,true,true,true,true,true,false,true] 2 [[false,false,false,true],[],[],[],[],[],[true,true,true,false,true],[],[],[],[],[],[],[true],[true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[false,true],[false,true],[true],[false,true,true,true,true,false,true,true,false,true],[true,false,true],[true,true,true,false,false,true,true],[false,true,false,true]] [true,false,true] 8 := by
  dsimp only [agrees]
  decide +kernel
#print axioms canonical_2

theorem canonical_3 : agrees 0 165603 5294881 [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true] [true,true,true,true,false,false,false,false,true,false,true] 2 [[false,false,true],[],[],[],[],[],[true,true,true,false,true],[],[],[],[],[],[],[false,true,true],[true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[false,true],[false,true,false,false,true],[true],[false,true,true,true,true,false,true,true,false,true],[true,true,true,false,false,true,true],[true,false,true],[false,true,false,true]] [true,false,true] 8 := by
  dsimp only [agrees]
  decide +kernel
#print axioms canonical_3

end ExplainableCrypto.Helios.Computational.PrimeHonestCiphertextControls
