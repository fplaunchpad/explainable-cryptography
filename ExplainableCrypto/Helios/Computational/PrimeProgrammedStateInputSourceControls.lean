import ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputSource
import ExplainableCrypto.Helios.Computational.BallotStateCodecControls

/-! Independently specified typed-state extraction controls. No native reduction axioms. -/
namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputSourceControls
open OracleComp BitOracleMachine BallotCacheCodecControls
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
attribute [local irreducible] BitOracleMachine.run

private def g : PrimeGroup 23 11 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (2 : ZMod 23) (by decide : (2 : ZMod 23)^11 = 1))
private def pk : PrimeGroup 23 11 := Additive.ofMul
  (rootsOfUnity.mkOfPowEq (4 : ZMod 23) (by decide : (4 : ZMod 23)^11 = 1))
private def state : BallotFiniteProgrammedState (ZMod 11) (PrimeGroup 23 11) :=
  ⟨cache,true,[key.1,otherKey.1,key.1,key.1]⟩
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
private def savedWord : List Bool := bitFieldsEncode
  [bitFieldsEncode [shadowWord,bitFieldsEncode [[true],historyWord]],liveWord]
private def rawWord : List Bool := bitFieldsEncode
  [uniformNatEncode 23,bitFieldsEncode [uniformNatEncode 2,uniformNatEncode 4],
   false :: uniformNatEncode 11,[true],savedWord]
private def generatedKey : List Bool := bitFieldsEncode ([2,4,8,13,16,3,9,12].map uniformNatEncode)
private def expectedWords : Fin 48 → List Bool :=
  ![(13 : Nat).bits,uniformNatEncode 2,(11 : Nat).bits,(16 : Nat).bits,[],[],(23 : Nat).bits,uniformNatEncode 0,[],[],
    uniformNatEncode 2,uniformNatEncode 0,uniformNatEncode 4,(3 : Nat).bits,rawWord,(4 : Nat).bits,(2 : Nat).bits,(8 : Nat).bits,
    [true],false :: uniformNatEncode 11,uniformNatEncode 3,uniformNatEncode 1,(10 : Nat).bits,
    [],[],[],[],[],[],[],[],[],[],[],[],[],[],[],(3 : Nat).bits,(18 : Nat).bits,(9 : Nat).bits,[],(12 : Nat).bits,generatedKey,
    shadowWord,liveWord,[true],historyWord]

/-- The expected bytes were constructed from literal numeric entries; both caches
are nonempty and unequal, and the history has ordered repetitions. -/
theorem literal_state_fields :
    PrimeProgrammedStateSource.saved state live = savedWord ∧
    (ballotCacheBitCodec 23 11).encode state.cache = shadowWord ∧
    (ballotCacheBitCodec 23 11).encode live = liveWord ∧
    (ballotStatementBitCodec 23 11).list.encode state.programmed = historyWord := by
  decide +kernel

theorem full_state_presentation :
    PrimeProgrammedStateInputMachine.sourceResult 0 g pk true state live draws =
      (⟨none,2,expectedWords⟩ : PrimeProgrammedStateInputMachine.Config) := by
  change (⟨_,_,_⟩ : PrimeProgrammedStateInputMachine.Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> decide +kernel

/-- Apply the checked actual execution; only the independently expected final
state is reduced, avoiding an enormous concrete machine execution in the kernel. -/
theorem extraction_full_state :
    ∃ charge ≤ PrimeProgrammedStateInputMachine.cost rawWord.length,
      BitOracleMachine.run PrimeProgrammedStateInputMachine.code
        (PrimeProgrammedStateInputMachine.clock rawWord.length)
        (PrimeProgrammedStateInputMachine.start
          (PrimeSimKeyCaller.sourceResult 0 g pk true
            (PrimeProgrammedStateSource.saved state live) draws).stk) =
      pure ((⟨none,2,expectedWords⟩ : PrimeProgrammedStateInputMachine.Config),charge) := by
  have hr : PrimeHonestInputMachine.input g pk 0 true
      (PrimeProgrammedStateSource.saved state live) = rawWord := by decide +kernel
  obtain ⟨charge,hc,he⟩ := PrimeProgrammedStateInputMachine.charged_source 0 g pk true state live draws
  rw [hr] at hc he
  rw [full_state_presentation] at he
  exact ⟨charge,hc,he⟩

theorem distinct_caches_not_swapped :
    (PrimeProgrammedStateInputMachine.sourceResult 0 g pk true state live draws).stk 44 ≠ liveWord ∧
    (PrimeProgrammedStateInputMachine.sourceResult 0 g pk true state live draws).stk 45 ≠ shadowWord := by
  rw [full_state_presentation]
  decide +kernel

theorem flag_not_cleared :
    (PrimeProgrammedStateInputMachine.sourceResult 0 g pk true state live draws).stk 46 ≠ [false] := by
  rw [full_state_presentation]
  decide

theorem history_not_reversed_or_deduplicated :
    (PrimeProgrammedStateInputMachine.sourceResult 0 g pk true state live draws).stk 47 ≠
      bitFieldsEncode [statementWord,statementWord,otherStatementWord,statementWord] ∧
    (PrimeProgrammedStateInputMachine.sourceResult 0 g pk true state live draws).stk 47 ≠
      bitFieldsEncode [statementWord,otherStatementWord] := by
  rw [full_state_presentation]
  decide +kernel

#print axioms literal_state_fields
#print axioms full_state_presentation
#print axioms extraction_full_state
#print axioms distinct_caches_not_swapped
#print axioms flag_not_cleared
#print axioms history_not_reversed_or_deduplicated
end ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputSourceControls
