import ExplainableCrypto.Helios.Computational.PrimeSimCommitMachineRun

/-! Independently derived controls for the first simulated commitment coordinate.
Literal full-state positives use the checked run theorem; eight actual mutation
boundaries compare altered instructions with the original controller. The native
harness separately checks complete traces of these mutations. -/

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitControls
open PrimeSimCommitMachine OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
set_option maxRecDepth 262144
set_option maxHeartbeats 0
set_option synthInstance.maxSize 512
private def mutated (m : Nat) (l : Fin size) : Command 38 size 3 :=
  if m == 1 && l == powerLabel 0 (BinaryModPower.copyLabel 0 0) then
    .compute (.load (fun _ => 2) (.goto (fun _ => 3)))
  else if m == 2 && l == powerLabel 1 (BinaryModPower.copyLabel 0 0) then
    .compute (.load (fun _ => 2) (.goto (fun _ => 4)))
  else if m == 3 && l == multiplyLabel (BinaryModMultiply.copyLabel 0) then
    .compute (.load (fun _ => 2) (.goto (fun _ => 5)))
  else if m == 4 && l.val >= 33 && l.val < 37 then
    match code l with
    | .compute s => .compute (TM2FiniteCoordinates.translate (Equiv.swap (9 : Fin 38) 1)
      (Equiv.refl _) (Equiv.refl _) s)
    | c => c
  else if m == 5 && l == 0 then
    .compute (.load (fun _ => 2) (.goto (fun _ => 1)))
  else if (m == 6 || m == 7) && l == 12 then
    match code l with
    | .compute s => .compute (.push (if m == 6 then 10 else 14) (fun _ => false) s)
    | c => c
  else if m == 8 && l == 6 then .compute (.goto (fun _ => 7))
  else code l

private def words (xs : List (Nat × List Bool)) : Fin 38 → List Bool :=
  fun k => ((xs.find? (fun p => p.1 == k.val)).map Prod.snd).getD []
private def once (m : Nat) (l : Fin size) (v : Fin 3) (w : Fin 38 → List Bool) : Config :=
  Turing.TM2.stepAux (match mutated m l with | .compute s => s | _ => .halt) v w
private def view (c : Config) := (c.l.map Fin.val,c.var.val,List.ofFn c.stk)

theorem omit_first_boundary :
    view (once 1 (powerLabel 0 (BinaryModPower.copyLabel 0 0)) 0 (words [(34,[true])])) =
      (some 3,2,List.ofFn (words [(34,[true])])) ∧
    (once 0 (powerLabel 0 (BinaryModPower.copyLabel 0 0)) 0 (words [(34,[true])])).l ≠ some 3 := by decide +kernel

theorem omit_second_boundary :
    view (once 2 (powerLabel 1 (BinaryModPower.copyLabel 0 0)) 0 (words [(34,[true])])) =
      (some 4,2,List.ofFn (words [(34,[true])])) ∧
    (once 0 (powerLabel 1 (BinaryModPower.copyLabel 0 0)) 0 (words [(34,[true])])).l ≠ some 4 := by decide +kernel

theorem omit_product_boundary :
    view (once 3 (multiplyLabel (BinaryModMultiply.copyLabel 0)) 0 (words [(31,[false,false,true]),(33,[false,true])])) =
      (some 5,2,List.ofFn (words [(31,[false,false,true]),(33,[false,true])])) ∧
    (once 0 (multiplyLabel (BinaryModMultiply.copyLabel 0)) 0 (words [(31,[false,false,true]),(33,[false,true])])).l ≠ some 5 := by decide +kernel

theorem positive_exponent_boundary :
    view (once 4 (transferLabel 5 1) 0 (words [(1,[true]),(9,[false,true])])) =
      (some 34,2,List.ofFn (words [(9,[false,true]),(26,[true])])) ∧
    view (once 0 (transferLabel 5 1) 0 (words [(1,[true]),(9,[false,true])])) =
      (some 34,1,List.ofFn (words [(1,[true]),(9,[true]),(26,[false])])) := by decide +kernel

theorem skip_complement_boundary :
    view (once 5 0 2 (words [(2,[true,true]),(11,[true,false,true])])) =
      (some 1,2,List.ofFn (words [(2,[true,true]),(11,[true,false,true])])) ∧
    (once 0 0 2 (words [(2,[true,true]),(11,[true,false,true])])).l = some 522 := by decide +kernel

theorem corrupt_c_boundary :
    view (once 6 12 0 (words [(10,[false])])) =
      (none,2,List.ofFn (words [(10,[false,false])])) ∧
    view (once 0 12 0 (words [(10,[false])])) =
      (none,2,List.ofFn (words [(10,[false])])) := by decide +kernel

theorem corrupt_context_boundary :
    view (once 7 12 0 (words [(14,[true,false,true])])) =
      (none,2,List.ofFn (words [(14,[false,true,false,true])])) ∧
    view (once 0 12 0 (words [(14,[true,false,true])])) =
      (none,2,List.ofFn (words [(14,[true,false,true])])) := by decide +kernel

theorem omit_modulus_clear_boundary :
    view (once 8 6 0 (words [(29,[true,true,true])])) =
      (some 7,0,List.ofFn (words [(29,[true,true,true])])) ∧
    view (once 0 6 0 (words [(29,[true,true,true])])) =
      (some 6,2,List.ofFn (words [(29,[true,true])])) := by decide +kernel

#print axioms omit_first_boundary
#print axioms omit_second_boundary
#print axioms omit_product_boundary
#print axioms positive_exponent_boundary
#print axioms skip_complement_boundary
#print axioms corrupt_c_boundary
#print axioms corrupt_context_boundary
#print axioms omit_modulus_clear_boundary
end ExplainableCrypto.Helios.Computational.PrimeSimCommitControls

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitControls
open PrimeSimCommitMachine
set_option maxRecDepth 262144
set_option maxHeartbeats 0
set_option synthInstance.maxSize 512
theorem zero_scalars_full_state :
    tick^[clock 3 2] (start ![[false,true],[],[false,true],[],[],[],[true,true],[true,false,true],[],[],[false],[false],[false],[true],[true,true,true,false,true,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,false,true,true,false,true,true,false,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[true],[false,true],[false,true],[true],[false,true,true,false,false,true],[true,false,true],[true,false,true],[true]]) =
      (⟨none,2,![[false,true],[],[false,true],[true],[],[],[true,true],[true,false,true],[],[],[false],[false],[false],[true],[true,true,true,false,true,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,false,true,true,false,true,true,false,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[true],[false,true],[false,true],[true],[false,true,true,false,false,true],[true,false,true],[true,false,true],[true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]⟩ : Config) := by
  have hi : inputWords 3 2 2 2 0 0 ![[false,true],[true,false,true],[false],[true],[true,true,true,false,true,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,false,true,true,false,true,true,false,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[true],[true],[false,true,true,false,false,true],[true,false,true],[true,false,true],[true]] = ![[false,true],[],[false,true],[],[],[],[true,true],[true,false,true],[],[],[false],[false],[false],[true],[true,true,true,false,true,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,false,true,true,false,true,true,false,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[true],[false,true],[false,true],[true],[false,true,true,false,false,true],[true,false,true],[true,false,true],[true]] := by decide +kernel
  have hr : result (answer 3 2 2 2 0 0).bits ![[false,true],[],[false,true],[],[],[],[true,true],[true,false,true],[],[],[false],[false],[false],[true],[true,true,true,false,true,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,false,true,true,false,true,true,false,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[true],[false,true],[false,true],[true],[false,true,true,false,false,true],[true,false,true],[true,false,true],[true]] =
      (⟨none,2,![[false,true],[],[false,true],[true],[],[],[true,true],[true,false,true],[],[],[false],[false],[false],[true],[true,true,true,false,true,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,false,true,true,false,true,true,false,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[true],[false,true],[false,true],[true],[false,true,true,false,false,true],[true,false,true],[true,false,true],[true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]⟩ : Config) := by
    apply congrArg (Turing.TM2.Cfg.mk none (2 : Fin 3))
    funext k
    fin_cases k <;> decide +kernel
  simpa only [hi,hr] using padded_run 3 2 2 2 0 0 (by decide) (by decide) (by decide) (by decide) (by decide) ![[false,true],[true,false,true],[false],[true],[true,true,true,false,true,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,false,true,true,false,true,true,false,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[true],[true],[false,true,true,false,false,true],[true,false,true],[true,false,true],[true]]
#print axioms zero_scalars_full_state
theorem sign_full_state :
    tick^[clock 7 3] (start ![[true],[],[true,true],[],[],[],[true,true,true],[true,true,false,false,true],[],[],[false],[true,false,true],[true,false,true],[true],[true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[false,true],[false,true],[true],[false,true,true,false,true,true],[true,false,true],[true,true,false,false,true],[false,true]]) =
      (⟨none,2,![[true],[],[true,true],[true],[],[],[true,true,true],[true,true,false,false,true],[],[],[false],[true,false,true],[true,false,true],[true],[true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[false,true],[false,true],[true],[false,true,true,false,true,true],[true,false,true],[true,true,false,false,true],[false,true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]⟩ : Config) := by
  have hi : inputWords 7 3 2 2 1 1 ![[true],[true,true,false,false,true],[false],[true],[true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[true],[false,true,true,false,true,true],[true,false,true],[true,true,false,false,true],[false,true]] = ![[true],[],[true,true],[],[],[],[true,true,true],[true,true,false,false,true],[],[],[false],[true,false,true],[true,false,true],[true],[true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[false,true],[false,true],[true],[false,true,true,false,true,true],[true,false,true],[true,true,false,false,true],[false,true]] := by decide +kernel
  have hr : result (answer 7 3 2 2 1 1).bits ![[true],[],[true,true],[],[],[],[true,true,true],[true,true,false,false,true],[],[],[false],[true,false,true],[true,false,true],[true],[true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[false,true],[false,true],[true],[false,true,true,false,true,true],[true,false,true],[true,true,false,false,true],[false,true]] =
      (⟨none,2,![[true],[],[true,true],[true],[],[],[true,true,true],[true,true,false,false,true],[],[],[false],[true,false,true],[true,false,true],[true],[true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[false,true],[false,true],[true],[false,true,true,false,true,true],[true,false,true],[true,true,false,false,true],[false,true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]⟩ : Config) := by
    apply congrArg (Turing.TM2.Cfg.mk none (2 : Fin 3))
    funext k
    fin_cases k <;> decide +kernel
  simpa only [hi,hr] using padded_run 7 3 2 2 1 1 (by decide) (by decide) (by decide) (by decide) (by decide) ![[true],[true,true,false,false,true],[false],[true],[true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[true],[false,true,true,false,true,true],[true,false,true],[true,true,false,false,true],[false,true]]
#print axioms sign_full_state
end ExplainableCrypto.Helios.Computational.PrimeSimCommitControls
