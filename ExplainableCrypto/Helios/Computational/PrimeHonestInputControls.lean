import ExplainableCrypto.Helios.Computational.PrimeHonestInputMachine

namespace ExplainableCrypto.Helios.Computational.PrimeHonestInputControls
open PrimeHonestInputMachine Turing.TM2
set_option maxRecDepth 262144
set_option maxHeartbeats 0
set_option synthInstance.maxSize 512
private def jump (l : Fin 97) : Stmt (fun _ : Fin 23 => Bool) (Fin 97) (Fin 3) :=
  .load (fun _ => 0) (.goto (fun _ => l))
private def mutated (m : Nat) (l : Fin 97) :=
  if m == 1 && l == copyLabel 0 then jump 0
  else if m == 2 && l.val >= 91 then
    TM2FiniteCoordinates.translate (Equiv.swap (15 : Fin 23) 16) (Equiv.refl _) (Equiv.refl _) (program l)
  else if m == 3 && l == 4 then .pop 7 (fun _ b => BinaryModuloCode.memory b)
    (.branch (fun v => v == 1) (jump 5) (.load (fun _ => 1) .halt))
  else if m == 4 && l == 13 then .pop 9 (fun _ b => BinaryModuloCode.memory b)
    (.branch (fun v => v == 2) (jump 14) (.load (fun _ => 1) .halt))
  else if m == 5 && l == 18 then .branch (fun v => v == 2)
    (jump (fieldLabel 4 0)) (.load (fun _ => 1) .halt)
  else if m == 6 && l == 20 then .branch (fun v => v == 2)
    (jump (fieldLabel 6 0)) (.load (fun _ => 1) .halt)
  else if m == 7 && l == 22 then .load (fun _ => 2) .halt
  else program l
private def execute (m : Nat) : Nat → Config → Nat → Nat → Config × Nat × Nat
  | 0,cfg,used,charge => (cfg,used,charge)
  | n+1,cfg,used,charge => match cfg.l with
    | none => (cfg,used,charge)
    | some l => execute m n (TM2ReturnLink.tick (mutated m) cfg) (used+1)
        (charge+BitOracleMachine.localCost (mutated m l))
private def observed (m fuel : Nat) (raw : List Bool) :=
  let out := execute m fuel (start raw) 0 0
  ((out.1.l,out.1.var.val,List.ofFn out.1.stk),out.2.1,out.2.2)
private def success (m fuel : Nat) (raw : List Bool) (ws : List (List Bool)) : Prop :=
  let out := observed m fuel raw
  out.1 = (none,2,ws) ∧ out.2.1 ≤ fuel ∧ out.2.2 ≤ 32*fuel
private def rejected (fuel : Nat) (raw : List Bool) : Prop :=
  let out := observed 0 fuel raw
  out.1.1 = none ∧ out.1.2.1 = 1 ∧ out.2.1 ≤ fuel
private def mutationChanges (m fuel : Nat) (raw : List Bool) (ws : List (List Bool)) : Prop :=
  let out := observed m fuel raw
  out.1.1 = none ∧ out.1 ≠ (none,2,ws) ∧ out.2.1 ≤ fuel
private def mutationRejects (m fuel : Nat) (raw : List Bool) : Prop :=
  let out := observed m fuel raw
  out.1.1 = none ∧ out.1.2.1 = 1 ∧ out.2.1 ≤ fuel
private def mutationAccepts (m fuel : Nat) (raw : List Bool) : Prop :=
  let out := observed m fuel raw
  out.1.1 = none ∧ out.1.2.1 = 2 ∧ out.2.1 ≤ fuel

theorem omitted_copy_counterexample : mutationChanges 1 145483 [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true] [[],[],[],[],[],[],[true,true,true,false,true],[],[],[],[],[],[],[],[true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[false,true],[],[true],[false,true,true,true,true,false,true,true,false,true],[],[],[]] := by
  dsimp only [success,rejected,mutationChanges,mutationAccepts,mutationRejects]
  decide +kernel
#print axioms omitted_copy_counterexample

theorem swapped_coordinates_counterexample : mutationChanges 2 145483 [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true] [[],[],[],[],[],[],[true,true,true,false,true],[],[],[],[],[],[],[],[true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[false,true],[],[true],[false,true,true,true,true,false,true,true,false,true],[],[],[]] := by
  dsimp only [success,rejected,mutationChanges,mutationAccepts,mutationRejects]
  decide +kernel
#print axioms swapped_coordinates_counterexample

theorem wrong_outer_arity_baseline_rejects : rejected 145483 [true,true,true,false,false,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true] := by
  dsimp only [success,rejected,mutationChanges,mutationAccepts,mutationRejects]
  decide +kernel
#print axioms wrong_outer_arity_baseline_rejects

theorem wrong_outer_arity_counterexample : mutationAccepts 3 145483 [true,true,true,false,false,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true] := by
  dsimp only [success,rejected,mutationChanges,mutationAccepts,mutationRejects]
  decide +kernel
#print axioms wrong_outer_arity_counterexample

theorem wrong_nested_arity_baseline_rejects : rejected 145483 [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true] := by
  dsimp only [success,rejected,mutationChanges,mutationAccepts,mutationRejects]
  decide +kernel
#print axioms wrong_nested_arity_baseline_rejects

theorem wrong_nested_arity_counterexample : mutationAccepts 4 145483 [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true] := by
  dsimp only [success,rejected,mutationChanges,mutationAccepts,mutationRejects]
  decide +kernel
#print axioms wrong_nested_arity_counterexample

theorem ignored_pk_suffix_baseline_rejects : rejected 160103 [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,true,false,false,true,false,false,false,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,true,false,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true] := by
  dsimp only [success,rejected,mutationChanges,mutationAccepts,mutationRejects]
  decide +kernel
#print axioms ignored_pk_suffix_baseline_rejects

theorem bypassed_pk_guard_still_rejects_counterexample : mutationRejects 5 160103 [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,true,false,false,true,false,false,false,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,true,false,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true] := by
  dsimp only [success,rejected,mutationChanges,mutationAccepts,mutationRejects]
  decide +kernel
#print axioms bypassed_pk_guard_still_rejects_counterexample

theorem ignored_nested_suffix_baseline_rejects : rejected 154171 [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,true,false,false,false,false,false,false,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true] := by
  dsimp only [success,rejected,mutationChanges,mutationAccepts,mutationRejects]
  decide +kernel
#print axioms ignored_nested_suffix_baseline_rejects

theorem ignored_nested_suffix_counterexample : mutationAccepts 5 154171 [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,true,false,false,false,false,false,false,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true] := by
  dsimp only [success,rejected,mutationChanges,mutationAccepts,mutationRejects]
  decide +kernel
#print axioms ignored_nested_suffix_counterexample

theorem nonsingleton_vote_baseline_rejects : rejected 154171 [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true] := by
  dsimp only [success,rejected,mutationChanges,mutationAccepts,mutationRejects]
  decide +kernel
#print axioms nonsingleton_vote_baseline_rejects

theorem nonsingleton_vote_counterexample : mutationAccepts 6 154171 [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true] := by
  dsimp only [success,rejected,mutationChanges,mutationAccepts,mutationRejects]
  decide +kernel
#print axioms nonsingleton_vote_counterexample

theorem uncleared_saved_counterexample : mutationChanges 7 145483 [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true] [[],[],[],[],[],[],[true,true,true,false,true],[],[],[],[],[],[],[],[true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[false,true],[],[true],[false,true,true,true,true,false,true,true,false,true],[],[],[]] := by
  dsimp only [success,rejected,mutationChanges,mutationAccepts,mutationRejects]
  decide +kernel
#print axioms uncleared_saved_counterexample

theorem literal_true_control : success 0 145483 [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true] [[],[],[],[],[],[],[true,true,true,false,true],[],[],[],[],[],[],[],[true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[false,true],[],[true],[false,true,true,true,true,false,true,true,false,true],[],[],[]] := by
  dsimp only [success,rejected,mutationChanges,mutationAccepts,mutationRejects]
  decide +kernel
#print axioms literal_true_control

theorem literal_false_empty_saved_control : success 0 126191 [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,false,false] [[],[],[],[],[],[],[true,true,true,false,true],[],[],[],[],[],[],[],[true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,false,false],[false,false,true],[false,true],[],[false],[false,true,true,true,true,false,true,true,false,true],[],[],[]] := by
  dsimp only [success,rejected,mutationChanges,mutationAccepts,mutationRejects]
  decide +kernel
#print axioms literal_false_empty_saved_control

def typedGenerator : PrimeGroup 23 11 := Additive.ofMul (rootsOfUnity.mkOfPowEq (2 : ZMod 23) (by decide : (2 : ZMod 23)^11 = 1))
 def typedKey : PrimeGroup 23 11 := Additive.ofMul (rootsOfUnity.mkOfPowEq (4 : ZMod 23) (by decide : (4 : ZMod 23)^11 = 1))

theorem typed_source_encoding : input typedGenerator typedKey 0 true [true,false,true] = [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true] := by
  dsimp only [success,rejected,mutationChanges,mutationAccepts,mutationRejects]
  decide +kernel
#print axioms typed_source_encoding

theorem typed_encoding_shape {p q : Nat} [NeZero p] [NeZero q] (g pk : PrimeGroup p q)
    (slack : Nat) (vote : Bool) (saved : List Bool) :
    input g pk slack vote saved = bitFieldsEncode [uniformNatEncode p,
      bitFieldsEncode [uniformNatEncode (primeGroupCoordinate g).val,uniformNatEncode (primeGroupCoordinate pk).val],
      SamplerOperands.input slack q [],[vote],saved] := rfl
#print axioms typed_encoding_shape

end ExplainableCrypto.Helios.Computational.PrimeHonestInputControls
