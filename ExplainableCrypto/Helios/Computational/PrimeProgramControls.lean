import ExplainableCrypto.Helios.Computational.PrimeProgramMachineRun
import ExplainableCrypto.Helios.Computational.BallotStateCodecControls

namespace ExplainableCrypto.Helios.Computational.PrimeProgramControls
open OracleComp BitOracleMachine BallotCacheCodecControls
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
attribute [local irreducible] BitOracleMachine.run
private def g : PrimeGroup 23 11 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (2 : ZMod 23) (by decide : (2 : ZMod 23)^11 = 1))
private def pk : PrimeGroup 23 11 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (4 : ZMod 23) (by decide : (4 : ZMod 23)^11 = 1))
private def live : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11) :=
  (∅ : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11)).insert key 3
private def draws : (ZMod 11 × ZMod 11) × (ZMod 11 × ZMod 11 × ZMod 11 × ZMod 11) :=
  ((3,1),(2,0,4,0))

/-- Independent numeric records, in original pair/list framing order. -/
private def keyWord : List Bool := bitFieldsEncode ([1,2,3,4,6,8,9,12].map uniformNatEncode)
private def otherKeyWord : List Bool := bitFieldsEncode ([2,1,3,4,6,8,9,12].map uniformNatEncode)
private def statementWord : List Bool := bitFieldsEncode
  [bitFieldsEncode [uniformNatEncode 1,uniformNatEncode 2],
   bitFieldsEncode [uniformNatEncode 3,uniformNatEncode 4]]
private def otherStatementWord : List Bool := bitFieldsEncode
  [bitFieldsEncode [uniformNatEncode 2,uniformNatEncode 1],
   bitFieldsEncode [uniformNatEncode 3,uniformNatEncode 4]]
private def shadowWord : List Bool := bitFieldsEncode
  [bitFieldsEncode [otherKeyWord,uniformNatEncode 5],bitFieldsEncode [keyWord,uniformNatEncode 3]]
private def liveWord : List Bool := bitFieldsEncode [bitFieldsEncode [keyWord,uniformNatEncode 3]]
private def historyWord : List Bool := bitFieldsEncode
  [statementWord,otherStatementWord,statementWord,statementWord]

private def coord (n : Nat) (h : (n : ZMod 23)^11=1) : PrimeGroup 23 11 :=
  Additive.ofMul (rootsOfUnity.mkOfPowEq (n : ZMod 23) h)
private def generatedTypedKey : BallotForkPoint (PrimeGroup 23 11) :=
  (⟨coord 2 (by decide),coord 4 (by decide),coord 8 (by decide),coord 13 (by decide)⟩,
   (coord 16 (by decide),coord 3 (by decide)),(coord 9 (by decide),coord 12 (by decide)))
private def occupiedCache : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11) :=
  (((∅ : BallotFiniteCache (ZMod 11) (PrimeGroup 23 11)).insert generatedTypedKey 2).insert key 3).insert otherKey 5
private def inputState (occupied bad : Bool) : BallotFiniteProgrammedState (ZMod 11) (PrimeGroup 23 11) :=
  ⟨if occupied then occupiedCache else cache,bad,[key.1,otherKey.1,key.1,key.1]⟩
private def generatedKeyWord : List Bool := bitFieldsEncode ([2,4,8,13,16,3,9,12].map uniformNatEncode)
private def generatedStatementWord : List Bool := bitFieldsEncode
  [bitFieldsEncode [uniformNatEncode 2,uniformNatEncode 4],
   bitFieldsEncode [uniformNatEncode 8,uniformNatEncode 13]]
private def occupiedWord : List Bool := bitFieldsEncode
  [bitFieldsEncode [otherKeyWord,uniformNatEncode 5],bitFieldsEncode [keyWord,uniformNatEncode 3],
   bitFieldsEncode [generatedKeyWord,uniformNatEncode 2]]
private def freshWord : List Bool := bitFieldsEncode
  [bitFieldsEncode [generatedKeyWord,uniformNatEncode 2],
   bitFieldsEncode [otherKeyWord,uniformNatEncode 5],bitFieldsEncode [keyWord,uniformNatEncode 3]]
private def nextHistoryWord : List Bool := bitFieldsEncode
  [generatedStatementWord,statementWord,otherStatementWord,statementWord,statementWord]
private def rawWord (occupied bad : Bool) : List Bool := bitFieldsEncode
  [uniformNatEncode 23,bitFieldsEncode [uniformNatEncode 2,uniformNatEncode 4],
   false :: uniformNatEncode 11,[true],bitFieldsEncode
     [bitFieldsEncode [if occupied then occupiedWord else shadowWord,
       bitFieldsEncode [[bad],historyWord]],liveWord]]
private def expectedWords (occupied bad : Bool) : Fin 48 → List Bool :=
  ![(13 : Nat).bits,uniformNatEncode 2,(11 : Nat).bits,(16 : Nat).bits,[],[],(23 : Nat).bits,uniformNatEncode 0,[],[],
    uniformNatEncode 2,uniformNatEncode 0,uniformNatEncode 4,(3 : Nat).bits,rawWord occupied bad,(4 : Nat).bits,(2 : Nat).bits,(8 : Nat).bits,
    [true],false :: uniformNatEncode 11,uniformNatEncode 3,uniformNatEncode 1,(10 : Nat).bits,
    [],[],[],[],[],[],[],[],[],[],[],[],[],[],[],(3 : Nat).bits,(18 : Nat).bits,(9 : Nat).bits,[],(12 : Nat).bits,generatedKeyWord,
    if occupied then occupiedWord else freshWord,liveWord,[bad || occupied],nextHistoryWord]

/-- The numeric key and repeated history were fixed independently of execution. -/
theorem literal_input_fields (occupied bad : Bool) :
    (ballotKeyBitCodec 23 11).encode generatedTypedKey = generatedKeyWord ∧
    (ballotCacheBitCodec 23 11).encode (inputState occupied bad).cache =
      (if occupied then occupiedWord else shadowWord) ∧
    (ballotStatementBitCodec 23 11).list.encode (inputState occupied bad).programmed = historyWord := by
  cases occupied <;> cases bad <;> decide +kernel

/-- All four collision/sticky-flag cases have independently specified complete48-port endpoints. -/
theorem full_state_presentation (occupied bad : Bool) :
    PrimeProgramMachine.sourceResult 0 g pk true (inputState occupied bad) live draws =
      (⟨none,2,expectedWords occupied bad⟩ : PrimeProgramMachine.Config) := by
  cases occupied <;> cases bad <;> change (⟨_,_,_⟩ : PrimeProgramMachine.Config) = ⟨_,_,_⟩
  all_goals congr 1; funext k; fin_cases k <;> decide +kernel

/-- Actual composed execution, with full endpoint and derived original-input charge cap. -/
theorem execution_full_state (occupied bad : Bool) :
    ∃ charge ≤ PrimeProgramMachine.cost 23 11 (rawWord occupied bad).length,
      BitOracleMachine.run PrimeProgramMachine.code
        (PrimeProgramMachine.clock 23 11 (rawWord occupied bad).length)
        (PrimeProgramMachine.start
          (PrimeProgrammedStateCaller.sourceResult 0 g pk true (inputState occupied bad) live draws).stk) =
      pure ((⟨none,2,expectedWords occupied bad⟩ : PrimeProgramMachine.Config),charge) := by
  have hr : PrimeHonestInputMachine.input g pk 0 true
      (PrimeProgrammedStateSource.saved (inputState occupied bad) live) = rawWord occupied bad := by
    cases occupied <;> cases bad <;> decide +kernel
  obtain ⟨charge,hc,he⟩ := PrimeProgramMachine.charged_source 0 g pk true (inputState occupied bad) live draws
  rw [hr] at hc he
  rw [full_state_presentation] at he
  exact ⟨charge,hc,he⟩

/-- Agreement with the occupied challenge does not suppress the collision flag. -/
theorem agreeing_collision_not_false :
    (PrimeProgramMachine.sourceResult 0 g pk true (inputState true false) live draws).stk 46 ≠ [false] := by
  rw [full_state_presentation]
  decide +kernel

/-- A fresh key cannot clear an already set sticky flag. -/
theorem fresh_does_not_clear_sticky :
    (PrimeProgramMachine.sourceResult 0 g pk true (inputState false true) live draws).stk 46 ≠ [false] := by
  rw [full_state_presentation]
  decide +kernel

/-- A fresh key with a clear flag excludes the universally-colliding shortcut. -/
theorem fresh_clear_not_true :
    (PrimeProgramMachine.sourceResult 0 g pk true (inputState false false) live draws).stk 46 ≠ [true] := by
  rw [full_state_presentation]
  decide +kernel

/-- The agreeing collision retains cache order rather than moving the occupied key to the head. -/
theorem collision_cache_not_reordered :
    (PrimeProgramMachine.sourceResult 0 g pk true (inputState true false) live draws).stk 44 ≠ freshWord := by
  rw [full_state_presentation]
  decide +kernel

/-- Exact prepend preserves old repetitions and their original order. -/
theorem history_not_appended_or_deduplicated :
    (PrimeProgramMachine.sourceResult 0 g pk true (inputState false false) live draws).stk 47 ≠
      bitFieldsEncode [statementWord,otherStatementWord,statementWord,statementWord,generatedStatementWord] ∧
    (PrimeProgramMachine.sourceResult 0 g pk true (inputState false false) live draws).stk 47 ≠
      bitFieldsEncode [generatedStatementWord,statementWord,otherStatementWord] := by
  rw [full_state_presentation]
  decide +kernel

/-- Distinct shadow/live caches remain in their own ports. -/
theorem live_not_updated_or_swapped :
    (PrimeProgramMachine.sourceResult 0 g pk true (inputState false false) live draws).stk 45 ≠ freshWord ∧
    (PrimeProgramMachine.sourceResult 0 g pk true (inputState false false) live draws).stk 44 ≠ liveWord := by
  rw [full_state_presentation]
  decide +kernel

#print axioms literal_input_fields
#print axioms full_state_presentation
#print axioms execution_full_state
#print axioms agreeing_collision_not_false
#print axioms fresh_does_not_clear_sticky
#print axioms fresh_clear_not_true
#print axioms collision_cache_not_reordered
#print axioms history_not_appended_or_deduplicated
#print axioms live_not_updated_or_swapped
end ExplainableCrypto.Helios.Computational.PrimeProgramControls
