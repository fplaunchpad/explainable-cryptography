import ExplainableCrypto.Helios.Computational.PrimeSimKeyMachineSource

/-! Independent full-state literals from integer/codec gate fixtures. These
controls apply the derived execution theorem, avoiding concrete machine unroll. -/
namespace ExplainableCrypto.Helios.Computational.PrimeSimKeyMachineControls
open OracleComp BitOracleMachine PrimeSimKeyMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
attribute [local irreducible] BitOracleMachine.run
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
instance : Fact (Nat.Prime 3) := ⟨by decide⟩
instance : Fact (Nat.Prime 23) := ⟨by decide⟩
instance : Fact (Nat.Prime 11) := ⟨by decide⟩
private def g3 : PrimeGroup 7 3 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (2 : ZMod 7) (by decide : (2 : ZMod 7)^3 = 1))
private def pk3 : PrimeGroup 7 3 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (4 : ZMod 7) (by decide : (4 : ZMod 7)^3 = 1))
private def g11 : PrimeGroup 23 11 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (2 : ZMod 23) (by decide : (2 : ZMod 23)^11 = 1))
private def pk11 : PrimeGroup 23 11 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (4 : ZMod 23) (by decide : (4 : ZMod 23)^11 = 1))

private def q3_true_distinct_words : Fin 44 → List Bool :=
  ![[true],
  [true,true,false,false,true],
  [true,true],
  [true],
  [],
  [],
  [true,true,true],
  [true,true,false,false,true],
  [],
  [],
  [false],
  [true,false,true],
  [true,false,true],
  [true],
  [true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,false,true],
  [false,false,true],
  [false,true],
  [false,true],
  [true],
  [false,true,true,false,true,true],
  [true,false,true],
  [true,true,false,false,true],
  [false,true],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [false,false,true],
  [false,false,true],
  [true],
  [],
  [true],
  [true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,false,true,true,true,false,true,true,true,false,true,true,true,false,true]]

theorem q3_true_distinct_full_state :
    Prod.fst <$> BitOracleMachine.run code (clock 7)
      (start (PrimeSimAllCommitCaller.sourceResult 0 g3 pk3 true [true,false,true] ((1,2),(0,1,1,2))).stk) =
        pure (⟨none,2,q3_true_distinct_words⟩ : Config) := by
  rw [source]
  congr 1
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext j
  fin_cases j <;> decide +kernel
#print axioms q3_true_distinct_full_state

private def q3_false_distinct_words : Fin 44 → List Bool :=
  ![[false,false,true],
  [true,true,false,false,true],
  [true,true],
  [false,true],
  [],
  [],
  [true,true,true],
  [true,true,false,false,true],
  [],
  [],
  [false],
  [true,false,true],
  [true,true,false,false,true],
  [true],
  [true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,false,true,true,false,true,true,false,true,true,true,false,true,false,true,true,false,true,true,true,false,true],
  [false,false,true],
  [false,true],
  [false,true],
  [false],
  [false,true,true,false,true,true],
  [true,false,true],
  [true,true,false,false,true],
  [false,true],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [false,false,true],
  [false,true],
  [true],
  [],
  [false,false,true],
  [true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true]]

theorem q3_false_distinct_full_state :
    Prod.fst <$> BitOracleMachine.run code (clock 7)
      (start (PrimeSimAllCommitCaller.sourceResult 0 g3 pk3 false [true,false,true] ((1,2),(0,1,2,2))).stk) =
        pure (⟨none,2,q3_false_distinct_words⟩ : Config) := by
  rw [source]
  congr 1
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext j
  fin_cases j <;> decide +kernel
#print axioms q3_false_distinct_full_state

private def q11_all_distinct_source_words : Fin 44 → List Bool :=
  ![[true,false,true,true],
  [true,true,false,false,true],
  [true,true,false,true],
  [false,false,false,false,true],
  [],
  [],
  [true,true,true,false,true],
  [false],
  [],
  [],
  [true,true,false,false,true],
  [false],
  [true,true,true,false,false,false,true],
  [true,true],
  [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true],
  [false,false,true],
  [false,true],
  [false,false,false,true],
  [true],
  [false,true,true,true,true,false,true,true,false,true],
  [true,true,false,true,true],
  [true,false,true],
  [false,true,false,true],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [true,true],
  [false,true,false,false,true],
  [true,false,false,true],
  [],
  [false,false,true,true],
  [true,true,true,true,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,false,false,false,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,true,false,true,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,false,false,true,true]]

theorem q11_all_distinct_source_full_state :
    Prod.fst <$> BitOracleMachine.run code (clock 23)
      (start (PrimeSimAllCommitCaller.sourceResult 0 g11 pk11 true [true,false,true] ((3,1),(2,0,4,0))).stk) =
        pure (⟨none,2,q11_all_distinct_source_words⟩ : Config) := by
  rw [source]
  congr 1
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext j
  fin_cases j <;> decide +kernel
#print axioms q11_all_distinct_source_full_state

private def beforeCount : Config := ⟨some 168,2,![[true,false,true,true],
  [true,true,false,false,true],
  [true,true,false,true],
  [false,false,false,false,true],
  [],
  [],
  [true,true,true,false,true],
  [false],
  [],
  [],
  [true,true,false,false,true],
  [false],
  [true,true,true,false,false,false,true],
  [true,true],
  [true,true,true,false,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,false,false,true,true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,true,false,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true],
  [false,false,true],
  [false,true],
  [false,false,false,true],
  [true],
  [false,true,true,true,true,false,true,true,false,true],
  [true,true,false,true,true],
  [true,false,true],
  [false,true,false,true],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [true,true],
  [false,true,false,false,true],
  [true,false,false,true],
  [],
  [false,false,true,true],
  [true,true,true,false,true,false,true,true,true,false,false,true,true,true,true,false,true,true,true,true,true,true,false,false,false,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,false,false,false,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,true,false,true,true,true,true,true,true,false,true,true,false,true,true,true,true,true,true,false,false,false,false,false,true,true,true,true,false,true,false,true,true,true,false,true,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,true,false,false,true,true,true,true,true,false,false,false,true,true]]⟩

/-- Paired actual final instruction: the original emits U8 and preserves context. -/
theorem count_guard_positive : tick beforeCount =
    (⟨none,2,q11_all_distinct_source_words⟩ : Config) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext j
  fin_cases j <;> decide +kernel

private def wrongCount (l : Fin 169) :=
  if l == 168 then
    (([true,true,true,false,true,true,true] : List Bool).foldl
      (fun s b => Turing.TM2.Stmt.push (43 : Fin 44) (fun _ : Fin 3 => b) s)
      (.load (fun _ => 2) .halt))
  else program l
private def corruptedContext (l : Fin 169) :=
  if l == 168 then Turing.TM2.Stmt.push (14 : Fin 44) (fun _ : Fin 3 => false) (program l)
  else program l

theorem wrong_count_negative : TM2ReturnLink.tick wrongCount beforeCount ≠
    (⟨none,2,q11_all_distinct_source_words⟩ : Config) := by
  intro he
  have h := congrArg (fun cfg : Config => cfg.stk 43) he
  have hn : (TM2ReturnLink.tick wrongCount beforeCount).stk 43 ≠ q11_all_distinct_source_words 43 := by decide +kernel
  exact hn h

theorem corrupted_context_negative : TM2ReturnLink.tick corruptedContext beforeCount ≠
    (⟨none,2,q11_all_distinct_source_words⟩ : Config) := by
  intro he
  have h := congrArg (fun cfg : Config => cfg.stk 14) he
  have hn : (TM2ReturnLink.tick corruptedContext beforeCount).stk 14 ≠ q11_all_distinct_source_words 14 := by decide +kernel
  exact hn h

#print axioms count_guard_positive
#print axioms wrong_count_negative
#print axioms corrupted_context_negative
end ExplainableCrypto.Helios.Computational.PrimeSimKeyMachineControls
