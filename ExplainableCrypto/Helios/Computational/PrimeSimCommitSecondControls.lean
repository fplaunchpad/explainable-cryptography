import ExplainableCrypto.Helios.Computational.PrimeSimCommitSecondMachineSource

/-! Literal full-state controls use the checked source law and independently
computed Python fixtures. Mutation boundaries reduce actual changed commands;
the native gate separately checks their complete executions. -/
namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitSecondControls
open PrimeSimCommitSecondMachine OracleComp BitOracleMachine
set_option maxRecDepth 262144
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 512
attribute [local irreducible] BitOracleMachine.run
instance : Fact (Nat.Prime 2) := ⟨by decide⟩
instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private def g2 : PrimeGroup 3 2 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (2 : ZMod 3) (by decide : (2 : ZMod 3)^2 = 1))
private def pk2 : PrimeGroup 3 2 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (1 : ZMod 3) (by decide : (1 : ZMod 3)^2 = 1))

/-- Independently fixed complete39-port result; original first answer is retained. -/
theorem q2_full_state :
    Prod.fst <$> BitOracleMachine.run code (clock 3 2) (start ![[false,true],[],[false,true],[true],[],[],[true,true],[false],[],[],[false],[true,false,true],[true,false,true],[true],[true,true,true,false,true,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,false,true,true,false,true,true,false,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[true],[false,true],[false,true],[true],[false,true,true,false,false,true],[true,false,true],[true,false,true],[true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]) =
      pure (⟨none,2,![[false,true],[],[false,true],[true],[],[],[true,true],[false],[],[],[false],[true,false,true],[true,false,true],[true],[true,true,true,false,true,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,false,true,true,false,true,true,false,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[true],[false,true],[false,true],[true],[false,true,true,false,false,true],[true,false,true],[true,false,true],[true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[false,true]]⟩ : Config) := by
  have hi : (PrimeSimCommitCaller.sourceResult 0 g2 pk2 true [true,false,true] (((1 : ZMod 2),1),(0,1,1,0))).stk = ![[false,true],[],[false,true],[true],[],[],[true,true],[false],[],[],[false],[true,false,true],[true,false,true],[true],[true,true,true,false,true,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,false,true,true,false,true,true,false,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[true],[false,true],[false,true],[true],[false,true,true,false,false,true],[true,false,true],[true,false,true],[true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]] := by decide +kernel
  have ho : sourceResult 0 g2 pk2 true [true,false,true] (((1 : ZMod 2),1),(0,1,1,0)) = (⟨none,2,![[false,true],[],[false,true],[true],[],[],[true,true],[false],[],[],[false],[true,false,true],[true,false,true],[true],[true,true,true,false,true,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,false,true,true,false,true,true,false,false,true,true,false,true,true,true,true,false,true,true,true,false,true],[true],[false,true],[false,true],[true],[false,true,true,false,false,true],[true,false,true],[true,false,true],[true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[false,true]]⟩ : Config) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    funext k
    fin_cases k <;> decide +kernel
  simpa only [hi,ho] using source 0 g2 pk2 true [true,false,true] (((1 : ZMod 2),1),(0,1,1,0))
#print axioms q2_full_state
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private def g3 : PrimeGroup 7 3 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (2 : ZMod 7) (by decide : (2 : ZMod 7)^3 = 1))
private def pk3 : PrimeGroup 7 3 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (4 : ZMod 7) (by decide : (4 : ZMod 7)^3 = 1))

/-- Independently fixed complete39-port result; original first answer is retained. -/
theorem q3_full_state :
    Prod.fst <$> BitOracleMachine.run code (clock 7 3) (start ![[true],[],[true,true],[true],[],[],[true,true,true],[true,true,false,false,true],[],[],[false],[true,false,true],[true,false,true],[true],[true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[false,true],[false,true],[true],[false,true,true,false,true,true],[true,false,true],[true,true,false,false,true],[false,true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]) =
      pure (⟨none,2,![[true],[],[true,true],[true],[],[],[true,true,true],[true,true,false,false,true],[],[],[false],[true,false,true],[true,false,true],[true],[true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[false,true],[false,true],[true],[false,true,true,false,true,true],[true,false,true],[true,true,false,false,true],[false,true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[false,false,true]]⟩ : Config) := by
  have hi : (PrimeSimCommitCaller.sourceResult 0 g3 pk3 true [true,false,true] (((1 : ZMod 3),2),(0,1,1,2))).stk = ![[true],[],[true,true],[true],[],[],[true,true,true],[true,true,false,false,true],[],[],[false],[true,false,true],[true,false,true],[true],[true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[false,true],[false,true],[true],[false,true,true,false,true,true],[true,false,true],[true,true,false,false,true],[false,true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]] := by decide +kernel
  have ho : sourceResult 0 g3 pk3 true [true,false,true] (((1 : ZMod 3),2),(0,1,1,2)) = (⟨none,2,![[true],[],[true,true],[true],[],[],[true,true,true],[true,true,false,false,true],[],[],[false],[true,false,true],[true,false,true],[true],[true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,false,true],[false,false,true],[false,true],[false,true],[true],[false,true,true,false,true,true],[true,false,true],[true,true,false,false,true],[false,true],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[false,false,true]]⟩ : Config) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    funext k
    fin_cases k <;> decide +kernel
  simpa only [hi,ho] using source 0 g3 pk3 true [true,false,true] (((1 : ZMod 3),2),(0,1,1,2))
#print axioms q3_full_state

end ExplainableCrypto.Helios.Computational.PrimeSimCommitSecondControls

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitSecondControls
open PrimeSimCommitSecondMachine OracleComp BitOracleMachine
set_option maxRecDepth 262144
set_option maxHeartbeats 400000
/-- The first three actual mutations in the independently run second-coordinate
harness: wrong base, wrong ciphertext component, and damaged saved first answer. -/
private def mutated (m : Nat) (l : Fin size) : Command 39 size 3 :=
  if (m == 1 && l.val >= 17 && l.val < 21) || (m == 2 && l.val >= 29 && l.val < 33) then
    match code l with
    | .compute s => .compute (TM2FiniteCoordinates.translate
        (if m == 1 then Equiv.swap (15 : Fin 39) 16 else Equiv.swap 0 17)
        (Equiv.refl _) (Equiv.refl _) s)
    | c => c
  else if m == 3 && l == 12 then
    match code l with
    | .compute s => .compute (.push 3 (fun _ => false) s)
    | c => c
  else code l

private def words (xs : List (Nat × List Bool)) : Fin 39 → List Bool :=
  fun k => ((xs.find? (fun p => p.1 == k.val)).map Prod.snd).getD []
private def once (m : Nat) (l : Fin size) (v : Fin 3) (w : Fin 39 → List Bool) : Config :=
  Turing.TM2.stepAux (match mutated m l with | .compute s => s | _ => .halt) v w
private def view (c : Config) := (c.l.map Fin.val,c.var.val,List.ofFn c.stk)

theorem wrong_public_key_boundary :
    view (once 1 18 0 (words [(15,[true]),(16,[false,true]),(3,[true,false])])) =
      (some 18,1,List.ofFn (words [(15,[true]),(16,[true]),(3,[true,false]),(26,[false])])) ∧
    view (once 0 18 0 (words [(15,[true]),(16,[false,true]),(3,[true,false])])) =
      (some 18,2,List.ofFn (words [(16,[false,true]),(3,[true,false]),(26,[true])])) := by
  decide +kernel

theorem wrong_beta_boundary :
    view (once 2 30 0 (words [(0,[false,true]),(17,[true]),(3,[true,false])])) =
      (some 30,2,List.ofFn (words [(0,[false,true]),(3,[true,false]),(26,[true])])) ∧
    view (once 0 30 0 (words [(0,[false,true]),(17,[true]),(3,[true,false])])) =
      (some 30,1,List.ofFn (words [(0,[true]),(17,[true]),(3,[true,false]),(26,[false])])) := by
  decide +kernel

theorem saved_first_coordinate_boundary :
    view (once 3 12 0 (words [(3,[true,false]),(38,[false,true])])) =
      (none,2,List.ofFn (words [(3,[false,true,false]),(38,[false,true])])) ∧
    view (once 0 12 0 (words [(3,[true,false]),(38,[false,true])])) =
      (none,2,List.ofFn (words [(3,[true,false]),(38,[false,true])])) := by
  decide +kernel

#print axioms wrong_public_key_boundary
#print axioms wrong_beta_boundary
#print axioms saved_first_coordinate_boundary
end ExplainableCrypto.Helios.Computational.PrimeSimCommitSecondControls
