import ExplainableCrypto.Helios.Computational.TranscriptScalarSave

namespace ExplainableCrypto.Helios.Computational.TranscriptScalarSaveControls
open Turing.TM2 TranscriptScalarSave
set_option maxRecDepth 65536
set_option maxHeartbeats 0
private def mutated (m : Nat) (j : Fin 3) (l : Fin 7) :=
  if m == 1 && l == 1 then .goto (fun _ => transferLabel 0)
  else if m == 2 && l == transferLabel 3 then .goto (fun _ => 6)
  else if m == 3 && l == transferLabel 0 then .goto (fun _ => 6)
  else if m == 4 && l == 6 then .push 14 (fun _ => false) (program j l)
  else if m == 5 && l == 0 then .goto (fun _ => 1)
  else program j l
private def observe (m : Nat) (j : Fin 3) (fuel : Nat) (cfg : Config) :=
  let out := (TM2ReturnLink.tick (mutated m j))^[fuel] cfg
  (out.l,out.var.val,List.ofFn out.stk)
theorem mutant_1 : observe 1 0 18 (start 0 [true,false,true] [true,true] ![[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true]]) = (none,2,[[false,false],[],[true,true],[false,true],[true,false],[false,true],[true,true],[],[false,false],[true,true],[true,false,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true]]) := by decide +kernel
#print axioms mutant_1

theorem mutant_2 : observe 2 0 18 (start 0 [true,false,true] [true,true] ![[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true]]) = (none,2,[[false,false],[],[],[false,true],[true,false],[false,true],[true,true],[true,false,true],[false,false],[true,true],[true,false,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true]]) := by decide +kernel
#print axioms mutant_2

theorem mutant_3 : observe 3 0 18 (start 0 [true,false,true] [true,true] ![[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true]]) = (none,2,[[false,false],[],[],[false,true],[true,false],[false,true],[true,true],[true,false,true],[false,false],[true,true],[],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true]]) := by decide +kernel
#print axioms mutant_3

theorem mutant_4 : observe 4 0 18 (start 0 [true,false,true] [true,true] ![[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true]]) = (none,2,[[false,false],[],[],[false,true],[true,false],[false,true],[true,true],[],[false,false],[true,true],[true,false,true],[false,true],[true,false],[false,true],[false,true,true],[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true]]) := by decide +kernel
#print axioms mutant_4

theorem mutant_5 : observe 5 0 18 ({start 0 [true,false,true] [true,true] ![[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true]] with var := 1}) = (none,2,[[false,false],[],[],[false,true],[true,false],[false,true],[true,true],[],[false,false],[true,true],[true,false,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true]]) := by decide +kernel
#print axioms mutant_5

theorem failure_guard : observe 0 0 18 ({start 0 [true,false,true] [true,true] ![[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true]] with var := 1}) = (none,1,[[false,false],[],[true,true],[false,true],[true,false],[false,true],[true,true],[true,false,true],[false,false],[true,true],[],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true],[false,true],[true,false],[false,true],[true,true],[false,false],[true,true]]) := by decide +kernel
#print axioms failure_guard

theorem canonical_0_0 : observe 0 0 7 (start 0 [] [] ![[true],[],[true,false],[true,false],[true,false,false],[false],[true,false,false],[true,true],[false,true,false],[false,true],[],[false,false,false],[true],[false,false,false],[true,false],[],[false,false],[],[false],[false,false]]) = (none,2,[[true],[],[],[true,false],[true,false],[true,false,false],[false],[],[true,false,false],[true,true],[],[false,true,false],[false,true],[],[false,false,false],[true],[false,false,false],[true,false],[],[false,false],[],[false],[false,false]]) := by decide +kernel
#print axioms canonical_0_0

theorem canonical_0_1 : observe 0 0 11 (start 0 [false] [false] ![[],[true],[],[true,false,false],[true,true],[true,true,true],[true,true,false],[false],[true,false,true],[true,false],[false],[false],[true,false],[],[false,false,true],[false,true,false],[true],[false,true,true],[false,false],[true,false]]) = (none,2,[[],[],[],[],[true,false,false],[true,true],[true,true,true],[],[true,true,false],[false],[false],[true,false,true],[true,false],[false],[false],[true,false],[],[false,false,true],[false,true,false],[true],[false,true,true],[false,false],[true,false]]) := by decide +kernel
#print axioms canonical_0_1

theorem canonical_0_2 : observe 0 0 15 (start 0 [true,false] [false,false] ![[true,true],[],[],[],[true],[false,true],[false,false,true],[false],[true,true,false],[],[false],[false,true,true],[],[false],[false],[],[],[true,false],[false,false,true],[]]) = (none,2,[[true,true],[],[],[],[],[true],[false,true],[],[false,false,true],[false],[true,false],[true,true,false],[],[false],[false,true,true],[],[false],[false],[],[],[true,false],[false,false,true],[]]) := by decide +kernel
#print axioms canonical_0_2

theorem canonical_0_3 : observe 0 0 19 (start 0 [true,false,false] [true,false,false] ![[],[true,true,false],[false,false,true],[false],[false],[],[],[],[true],[true,true,false],[false,true],[],[false],[true],[],[true,false],[true,false,true],[true,true,true],[],[]]) = (none,2,[[],[],[],[false,false,true],[false],[false],[],[],[],[],[true,false,false],[true],[true,true,false],[false,true],[],[false],[true],[],[true,false],[true,false,true],[true,true,true],[],[]]) := by decide +kernel
#print axioms canonical_0_3

theorem canonical_0_4 : observe 0 0 19 (start 0 [false,false,false,false] [] ![[true],[],[],[true,true],[true,true],[false,false,true],[true],[false,true],[false,false,true],[],[],[false],[false],[true,false,true],[false,false,false],[],[],[false,true],[true,true,true],[false,true,false]]) = (none,2,[[true],[],[],[],[true,true],[true,true],[false,false,true],[],[true],[false,true],[false,false,false,false],[false,false,true],[],[],[false],[false],[true,false,true],[false,false,false],[],[],[false,true],[true,true,true],[false,true,false]]) := by decide +kernel
#print axioms canonical_0_4

theorem canonical_0_5 : observe 0 0 23 (start 0 [false,true,false,false,false] [true] ![[],[],[true,false],[false],[false,false],[false,false],[true,false,false],[false,true],[true,false,false],[true,false],[false],[false,true,false],[true,true,true],[],[true,false],[],[true],[true,false],[false],[false]]) = (none,2,[[],[],[],[true,false],[false],[false,false],[false,false],[],[true,false,false],[false,true],[false,true,false,false,false],[true,false,false],[true,false],[false],[false,true,false],[true,true,true],[],[true,false],[],[true],[true,false],[false],[false]]) := by decide +kernel
#print axioms canonical_0_5

theorem canonical_1_0 : observe 0 1 7 (start 1 [] [] ![[false,false],[false,true],[false,false],[true,true,true],[true,true],[true,false],[false,false,false],[false,true,false],[true,false],[],[],[true,false,false],[false,true],[true,false],[],[true],[true],[],[true],[]]) = (none,2,[[false,false],[],[],[false,false],[true,true,true],[true,true],[true,false],[],[false,false,false],[false,true,false],[true,false],[],[],[],[true,false,false],[false,true],[true,false],[],[true],[true],[],[true],[]]) := by decide +kernel
#print axioms canonical_1_0

theorem canonical_1_1 : observe 0 1 11 (start 1 [true] [true] ![[true],[],[false],[false,true],[],[false,true],[false,false,false],[false],[],[],[false,false],[],[],[],[],[false],[true,false],[],[true,false,true],[true]]) = (none,2,[[true],[],[],[false],[false,true],[],[false,true],[],[false,false,false],[false],[],[true],[],[false,false],[],[],[],[],[false],[true,false],[],[true,false,true],[true]]) := by decide +kernel
#print axioms canonical_1_1

theorem canonical_1_2 : observe 0 1 15 (start 1 [true,false] [true,true] ![[false,true],[true,false,false],[false,true,false],[],[false],[],[],[true],[],[true,true],[false,true],[true,false],[true],[false],[false,true],[],[false,true,true],[],[true],[]]) = (none,2,[[false,true],[],[],[false,true,false],[],[false],[],[],[],[true],[],[true,false],[true,true],[false,true],[true,false],[true],[false],[false,true],[],[false,true,true],[],[true],[]]) := by decide +kernel
#print axioms canonical_1_2

theorem canonical_1_3 : observe 0 1 19 (start 1 [true,true,true] [false,true,true] ![[true,true],[false,false,true],[true],[],[true,false],[],[true,true,false],[],[],[],[],[false],[true,false],[true],[true,false],[true,false],[false],[],[true],[true,false,false]]) = (none,2,[[true,true],[],[],[true],[],[true,false],[],[],[true,true,false],[],[],[true,true,true],[],[],[false],[true,false],[true],[true,false],[true,false],[false],[],[true],[true,false,false]]) := by decide +kernel
#print axioms canonical_1_3

theorem canonical_1_4 : observe 0 1 19 (start 1 [true,true,true,false] [] ![[false,true],[],[false],[false,false,false],[],[true],[false,false,false],[true],[false,true],[],[true,true,true],[],[false],[false,false],[],[false],[],[false,false,false],[true],[false,true,true]]) = (none,2,[[false,true],[],[],[false],[false,false,false],[],[true],[],[false,false,false],[true],[false,true],[true,true,true,false],[],[true,true,true],[],[false],[false,false],[],[false],[],[false,false,false],[true],[false,true,true]]) := by decide +kernel
#print axioms canonical_1_4

theorem canonical_1_5 : observe 0 1 23 (start 1 [false,true,true,true,false] [true] ![[true,true,true],[],[true,false,true],[true,true],[false],[true,true,true],[],[false,true,false],[false,true],[false,true,false],[],[true],[false,false],[true,true],[],[true],[false,false,false],[],[],[false,false,false]]) = (none,2,[[true,true,true],[],[],[true,false,true],[true,true],[false],[true,true,true],[],[],[false,true,false],[false,true],[false,true,true,true,false],[false,true,false],[],[true],[false,false],[true,true],[],[true],[false,false,false],[],[],[false,false,false]]) := by decide +kernel
#print axioms canonical_1_5

theorem canonical_2_0 : observe 0 2 7 (start 2 [] [] ![[false,false],[],[true,true,false],[true],[false],[false,true],[],[false,false,true],[true],[true,true,false],[false,false,true],[false],[],[],[],[],[],[false,true],[],[false]]) = (none,2,[[false,false],[],[],[true,true,false],[true],[false],[false,true],[],[],[false,false,true],[true],[true,true,false],[],[false,false,true],[false],[],[],[],[],[],[false,true],[],[false]]) := by decide +kernel
#print axioms canonical_2_0

theorem canonical_2_1 : observe 0 2 11 (start 2 [false] [true] ![[],[true,true,true],[],[true,true,false],[false,false,false],[false,false],[true,false,false],[true,false,true],[true,true,false],[false,false],[false,false,false],[true],[true,false],[],[false,true],[true],[true,false,true],[],[],[true,true,false]]) = (none,2,[[],[],[],[],[true,true,false],[false,false,false],[false,false],[],[true,false,false],[true,false,true],[true,true,false],[false,false],[false],[false,false,false],[true],[true,false],[],[false,true],[true],[true,false,true],[],[],[true,true,false]]) := by decide +kernel
#print axioms canonical_2_1

theorem canonical_2_2 : observe 0 2 15 (start 2 [false,true] [false,false] ![[false,true,true],[true,false,true],[false],[false,false],[],[false,true,true],[],[],[false],[true,false,false],[false,false],[true],[],[true,true],[false,false,false],[false,false,false],[false],[true,true,false],[false,true],[false,true,true]]) = (none,2,[[false,true,true],[],[],[false],[false,false],[],[false,true,true],[],[],[],[false],[true,false,false],[false,true],[false,false],[true],[],[true,true],[false,false,false],[false,false,false],[false],[true,true,false],[false,true],[false,true,true]]) := by decide +kernel
#print axioms canonical_2_2

theorem canonical_2_3 : observe 0 2 19 (start 2 [false,true,false] [false,true,true] ![[true,false],[true,false,false],[false,true],[true],[true,false],[true],[false],[],[],[false,false],[],[false,true,true],[false,false,false],[true],[true],[false],[false,false,true],[true,true],[false,true],[false,false]]) = (none,2,[[true,false],[],[],[false,true],[true],[true,false],[true],[],[false],[],[],[false,false],[false,true,false],[],[false,true,true],[false,false,false],[true],[true],[false],[false,false,true],[true,true],[false,true],[false,false]]) := by decide +kernel
#print axioms canonical_2_3

theorem canonical_2_4 : observe 0 2 19 (start 2 [false,false,true,true] [] ![[],[],[],[true,false,true],[false],[],[true,true],[],[],[false],[true,false,true],[false,false],[],[true,false],[true,true,true],[false,true,false],[true],[true],[true,false,false],[true,false]]) = (none,2,[[],[],[],[],[true,false,true],[false],[],[],[true,true],[],[],[false],[false,false,true,true],[true,false,true],[false,false],[],[true,false],[true,true,true],[false,true,false],[true],[true],[true,false,false],[true,false]]) := by decide +kernel
#print axioms canonical_2_4

theorem canonical_2_5 : observe 0 2 23 (start 2 [true,false,false,false,false] [true] ![[true,false],[false],[false,false],[false,false,true],[],[false,true],[false],[false,true,true],[true,true],[true],[false,true],[true,true],[false,true],[],[true],[false,true,false],[true,true],[true],[false,true,true],[false,false]]) = (none,2,[[true,false],[],[],[false,false],[false,false,true],[],[false,true],[],[false],[false,true,true],[true,true],[true],[true,false,false,false,false],[false,true],[true,true],[false,true],[],[true],[false,true,false],[true,true],[true],[false,true,true],[false,false]]) := by decide +kernel
#print axioms canonical_2_5
end ExplainableCrypto.Helios.Computational.TranscriptScalarSaveControls
