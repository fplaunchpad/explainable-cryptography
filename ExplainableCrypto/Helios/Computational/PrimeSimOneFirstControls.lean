import ExplainableCrypto.Helios.Computational.PrimeSimOneFirstMachineSource
namespace ExplainableCrypto.Helios.Computational.PrimeSimOneFirstControls
open PrimeSimOneFirstMachine OracleComp BitOracleMachine
set_option maxRecDepth 262144
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 512
attribute [local irreducible] BitOracleMachine.run
instance : Fact (Nat.Prime 2) := ⟨by decide⟩
instance : Fact (Nat.Prime 3) := ⟨by decide⟩
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private def g2 : PrimeGroup 3 2 := Additive.ofMul (rootsOfUnity.mkOfPowEq (2 : ZMod 3) (by decide : (2 : ZMod 3)^2=1))
private def pk2 : PrimeGroup 3 2 := Additive.ofMul (rootsOfUnity.mkOfPowEq (1 : ZMod 3) (by decide : (1 : ZMod 3)^2=1))
/-- Independent modular-arithmetic fixture checks every old word, new answer40 and empty scratch41. -/
theorem q2_full_state :
    Prod.fst <$> BitOracleMachine.run code (clock 3 2) (start ![[false,true],[true,false,true],[false,true],[true],[],[],[true,true],[false],[],[],[false],[true,false,true],[true,false,true],[true],[true,true,true,false,true,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,false,true,true,false,true,true,false,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[true],[false,true],[false,true],[true],[false,true,true,false,false,true],[true,false,true],[true,false,true],[true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[false,true],[true]]) =
      pure (⟨none,2,![[false,true],[true,false,true],[false,true],[true],[],[],[true,true],[false],[],[],[false],[true,false,true],[true,false,true],[true],[true,true,true,false,true,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,false,true,true,false,true,true,false,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[true],[false,true],[false,true],[true],[false,true,true,false,false,true],[true,false,true],[true,false,true],[true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[false,true],[true],[false,true],[]]⟩ : Config) := by
  have hi : (PrimeAdjustedBetaMachine.sourceResult 0 g2 pk2 true [true,false,true] (((1 : ZMod 2),1),(0,1,1,0))).stk = ![[false,true],[true,false,true],[false,true],[true],[],[],[true,true],[false],[],[],[false],[true,false,true],[true,false,true],[true],[true,true,true,false,true,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,false,true,true,false,true,true,false,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[true],[false,true],[false,true],[true],[false,true,true,false,false,true],[true,false,true],[true,false,true],[true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[false,true],[true]] := by decide +kernel
  have ho : sourceResult 0 g2 pk2 true [true,false,true] (((1 : ZMod 2),1),(0,1,1,0)) = (⟨none,2,![[false,true],[true,false,true],[false,true],[true],[],[],[true,true],[false],[],[],[false],[true,false,true],[true,false,true],[true],[true,true,true,false,true,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,false,true,true,false,true,true,false,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[true],[false,true],[false,true],[true],[false,true,true,false,false,true],[true,false,true],[true,false,true],[true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[false,true],[true],[false,true],[]]⟩ : Config) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    funext k
    fin_cases k <;> decide +kernel
  simpa only [hi,ho] using source 0 g2 pk2 true [true,false,true] (((1 : ZMod 2),1),(0,1,1,0))
#print axioms q2_full_state
private def g3 : PrimeGroup 7 3 := Additive.ofMul (rootsOfUnity.mkOfPowEq (2 : ZMod 7) (by decide : (2 : ZMod 7)^3=1))
private def pk3 : PrimeGroup 7 3 := Additive.ofMul (rootsOfUnity.mkOfPowEq (4 : ZMod 7) (by decide : (4 : ZMod 7)^3=1))
/-- Independent modular-arithmetic fixture checks every old word, new answer40 and empty scratch41. -/
theorem q3_full_state :
    Prod.fst <$> BitOracleMachine.run code (clock 7 3) (start ![[true],[true,true,false,false,true],[true,true],[true],[],[],[true,true,true],[true,true,false,false,true],[],[],[false],[true,false,true],[true,false,true],[true],[true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[false,true],[false,true],[true],[false,true,true,false,true,true],[true,false,true],[true,true,false,false,true],[false,true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[false,false,true],[false,false,true]]) =
      pure (⟨none,2,![[true],[true,true,false,false,true],[true,true],[true],[],[],[true,true,true],[true,true,false,false,true],[],[],[false],[true,false,true],[true,false,true],[true],[true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[false,true],[false,true],[true],[false,true,true,false,true,true],[true,false,true],[true,true,false,false,true],[false,true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[false,false,true],[false,false,true],[true],[]]⟩ : Config) := by
  have hi : (PrimeAdjustedBetaMachine.sourceResult 0 g3 pk3 true [true,false,true] (((1 : ZMod 3),2),(0,1,1,2))).stk = ![[true],[true,true,false,false,true],[true,true],[true],[],[],[true,true,true],[true,true,false,false,true],[],[],[false],[true,false,true],[true,false,true],[true],[true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[false,true],[false,true],[true],[false,true,true,false,true,true],[true,false,true],[true,true,false,false,true],[false,true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[false,false,true],[false,false,true]] := by decide +kernel
  have ho : sourceResult 0 g3 pk3 true [true,false,true] (((1 : ZMod 3),2),(0,1,1,2)) = (⟨none,2,![[true],[true,true,false,false,true],[true,true],[true],[],[],[true,true,true],[true,true,false,false,true],[],[],[false],[true,false,true],[true,false,true],[true],[true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[false,true],[false,true],[true],[false,true,true,false,true,true],[true,false,true],[true,true,false,false,true],[false,true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[false,false,true],[false,false,true],[true],[]]⟩ : Config) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    funext k
    fin_cases k <;> decide +kernel
  simpa only [hi,ho] using source 0 g3 pk3 true [true,false,true] (((1 : ZMod 3),2),(0,1,1,2))
#print axioms q3_full_state

private def words (xs : List (Nat × List Bool)) : Fin 42 → List Bool :=
  fun k => ((xs.find? (fun p => p.1 == k.val)).map Prod.snd).getD []
private def view (c : Config) := (c.l.map Fin.val,c.var.val,List.ofFn c.stk)

/-- Actual native-gate mutation5 corrupts the saved zero-branch A at final halt. -/
theorem corrupted_prior_first_A_boundary :
    view (Turing.TM2.stepAux (.push 3 (fun _ => false) (program 12)) 0
      (words [(1,[true]),(3,[true,false]),(40,[false,true])])) =
      (none,2,List.ofFn (words [(1,[true]),(3,[false,true,false]),(40,[false,true])])) ∧
    view (Turing.TM2.stepAux (program 12) 0
      (words [(1,[true]),(3,[true,false]),(40,[false,true])])) =
      (none,2,List.ofFn (words [(1,[true]),(3,[true,false]),(40,[false,true])])) := by
  decide +kernel

/-- Actual native-gate mutation6 omits the executed cleanup of scratch41. -/
theorem omitted_scratch_cleanup_boundary :
    view (Turing.TM2.stepAux (.goto (fun _ => 11)) 0
      (words [(1,[true]),(40,[false,true]),(41,[true])])) =
      (some 11,0,List.ofFn (words [(1,[true]),(40,[false,true]),(41,[true])])) ∧
    view (Turing.TM2.stepAux (program 10) 0
      (words [(1,[true]),(40,[false,true]),(41,[true])])) =
      (some 10,2,List.ofFn (words [(1,[true]),(40,[false,true])])) := by
  decide +kernel
#print axioms corrupted_prior_first_A_boundary
#print axioms omitted_scratch_cleanup_boundary
end ExplainableCrypto.Helios.Computational.PrimeSimOneFirstControls
