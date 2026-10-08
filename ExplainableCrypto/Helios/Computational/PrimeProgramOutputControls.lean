import ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachineSource
import ExplainableCrypto.Helios.Computational.PrimeProgramOutputCallerSource
import ExplainableCrypto.Helios.Computational.BallotStateCodecControls

namespace ExplainableCrypto.Helios.Computational.PrimeProgramOutputControls
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


private def proofWord : List Bool := bitFieldsEncode
  [bitFieldsEncode [bitFieldsEncode [uniformNatEncode 16,uniformNatEncode 3],
      bitFieldsEncode [uniformNatEncode 0,uniformNatEncode 4]],
   bitFieldsEncode [bitFieldsEncode [uniformNatEncode 9,uniformNatEncode 12],
      bitFieldsEncode [uniformNatEncode 2,uniformNatEncode 0]]]
private def savedWord (occupied bad : Bool) : List Bool := bitFieldsEncode
  [bitFieldsEncode [if occupied then occupiedWord else freshWord,
    bitFieldsEncode [[bad || occupied],nextHistoryWord]],liveWord]
private def oldSavedWord (occupied bad : Bool) : List Bool := bitFieldsEncode
  [bitFieldsEncode [if occupied then occupiedWord else shadowWord,
    bitFieldsEncode [[bad],historyWord]],liveWord]
private def expectedFullWords (occupied bad : Bool) : Fin 50 → List Bool := fun k =>
  if h : k.val < 48 then expectedWords occupied bad ⟨k.val,h⟩
  else if k=48 then proofWord else savedWord occupied bad

/-- Independently spelled seven-pair proof, including zero scalar records. -/
theorem literal_proof_word :
    (ballotProofBitCodec 23 11).encode (PrimeProgramProofSource.proof g pk true draws) = proofWord := by
  decide +kernel

/-- The occupied agreeing fixture keeps its cache order, while fresh insertion
prepends the key; both prepend a statement and keep the separate live cache. -/
theorem literal_saved_word (occupied bad : Bool) :
    (ballotBothCachesBitCodec 23 11).encode
      (PrimeProgramRepackSource.nextState g pk true (inputState occupied bad) draws,live) = savedWord occupied bad := by
  cases occupied <;> cases bad <;> decide +kernel

/-- All50 words are independently specified for all four sticky/collision cases. -/
theorem full_state_presentation (occupied bad : Bool) :
    PrimeProgramOutputMachine.sourceResult 0 g pk true (inputState occupied bad) live draws =
      (⟨none,2,expectedFullWords occupied bad⟩ : PrimeProgramOutputMachine.Config) := by
  cases occupied <;> cases bad <;> change (⟨_,_,_⟩ : PrimeProgramOutputMachine.Config) = ⟨_,_,_⟩
  all_goals congr 1; funext k; fin_cases k <;> decide +kernel

/-- Checked execution constructs the records; this is more than endpoint presentation. -/
theorem execution_full_state (occupied bad : Bool) :
    ∃ charge ≤ PrimeProgramOutputMachine.cost 23 11 (rawWord occupied bad).length,
      BitOracleMachine.run PrimeProgramOutputMachine.code
        (PrimeProgramOutputMachine.clock 23 11 (rawWord occupied bad).length)
        (PrimeProgramOutputMachine.start
          (PrimeProgramCaller.sourceResult 0 g pk true (inputState occupied bad) live draws).stk) =
      pure ((⟨none,2,expectedFullWords occupied bad⟩ : PrimeProgramOutputMachine.Config),charge) := by
  have hr : PrimeHonestInputMachine.input g pk 0 true
      (PrimeProgrammedStateSource.saved (inputState occupied bad) live) = rawWord occupied bad := by
    cases occupied <;> cases bad <;> decide +kernel
  obtain ⟨charge,hc,he⟩ := PrimeProgramOutputMachine.charged_source 0 g pk true (inputState occupied bad) live draws
  rw [hr] at hc he
  rw [full_state_presentation] at he
  exact ⟨charge,hc,he⟩

/-- The original raw caller transports that complete endpoint without changing a port. -/
theorem caller_full_state_presentation (occupied bad : Bool) :
    PrimeProgramOutputCaller.sourceResult 0 g pk true (inputState occupied bad) live draws =
      (⟨none,2,expectedFullWords occupied bad⟩ : PrimeProgramOutputCaller.Config) := by
  unfold PrimeProgramOutputCaller.sourceResult
  rw [full_state_presentation]
  rfl

/-- Original raw context, both nonce prefixes and the challenge/key remain resident. -/
theorem caller_retained_raw_nonces (occupied bad : Bool) :
    let cfg := PrimeProgramOutputCaller.sourceResult 0 g pk true (inputState occupied bad) live draws
    cfg.stk 14 = rawWord occupied bad ∧ cfg.stk 20 = uniformNatEncode 3 ∧
    cfg.stk 21 = uniformNatEncode 1 ∧ cfg.stk 10 = uniformNatEncode 2 ∧ cfg.stk 43 = generatedKeyWord := by
  dsimp only
  rw [caller_full_state_presentation]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- The new encoded saved state cannot be the old payload retained inside raw14. -/
theorem saved_changed (occupied bad : Bool) :
    (PrimeProgramOutputCaller.sourceResult 0 g pk true (inputState occupied bad) live draws).stk 49 ≠
      oldSavedWord occupied bad := by
  rw [caller_full_state_presentation]
  cases occupied <;> cases bad <;> decide +kernel

/-- Agreeing challenge2 still records a collision in both resident and serialized state. -/
theorem agreeing_collision_saved_flag :
    (PrimeProgramOutputCaller.sourceResult 0 g pk true (inputState true false) live draws).stk 46 = [true] ∧
    (PrimeProgramOutputCaller.sourceResult 0 g pk true (inputState true false) live draws).stk 49 ≠
      bitFieldsEncode [bitFieldsEncode [occupiedWord,bitFieldsEncode [[false],nextHistoryWord]],liveWord] := by
  rw [caller_full_state_presentation]
  decide +kernel

/-- A fresh update retains an already set sticky flag in the serialized return. -/
theorem fresh_sticky_saved_flag :
    (PrimeProgramOutputCaller.sourceResult 0 g pk true (inputState false true) live draws).stk 49 ≠
      bitFieldsEncode [bitFieldsEncode [freshWord,bitFieldsEncode [[false],nextHistoryWord]],liveWord] := by
  rw [caller_full_state_presentation]
  decide +kernel

/-- The proof is a nested branch record, not the flat list of its coordinates. -/
theorem proof_not_flattened :
    (PrimeProgramOutputCaller.sourceResult 0 g pk true (inputState false false) live draws).stk 48 ≠
      bitFieldsEncode ([16,3,0,4,9,12,2,0].map uniformNatEncode) := by
  rw [caller_full_state_presentation]
  decide +kernel

/-- The returned proof and updated saved-state words have distinct designated ports. -/
theorem returned_words_not_swapped :
    (PrimeProgramOutputCaller.sourceResult 0 g pk true (inputState false false) live draws).stk 48 ≠ savedWord false false ∧
    (PrimeProgramOutputCaller.sourceResult 0 g pk true (inputState false false) live draws).stk 49 ≠ proofWord := by
  rw [caller_full_state_presentation]
  decide +kernel

#print axioms literal_proof_word
#print axioms literal_saved_word
#print axioms full_state_presentation
#print axioms execution_full_state
#print axioms caller_full_state_presentation
#print axioms caller_retained_raw_nonces
#print axioms saved_changed
#print axioms agreeing_collision_saved_flag
#print axioms fresh_sticky_saved_flag
#print axioms proof_not_flattened
#print axioms returned_words_not_swapped
end ExplainableCrypto.Helios.Computational.PrimeProgramOutputControls
