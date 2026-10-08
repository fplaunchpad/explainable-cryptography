import ExplainableCrypto.Helios.Computational.PrimeSecondCommitMachineSource
import ExplainableCrypto.Helios.Computational.PrimeSecondTranscriptControls
import ExplainableCrypto.Helios.Computational.PrimeProgramOutputControls
import ExplainableCrypto.Helios.Computational.BallotStateCodecControls

namespace ExplainableCrypto.Helios.Computational.PrimeSecondCommitControls
open OracleComp BitOracleMachine BallotCacheCodecControls
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
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

private def newScalars : ZMod 11 × ZMod 11 × ZMod 11 × ZMod 11 := (0,1,10,0)
/-- New values are independently computed from g=2,pk=4,r2=1 and message zero.
All old50 words use the already audited literal predecessor fixture. -/
private def expectedSecondWords (occupied bad : Bool) : Fin 59 → List Bool := fun k =>
  if h : k.val < 50 then expectedFullWords occupied bad ⟨k.val,h⟩
  else (![ (2 : Nat).bits,(4 : Nat).bits,(1 : Nat).bits,[false],
      uniformNatEncode 0,uniformNatEncode 1,uniformNatEncode 10,uniformNatEncode 0,(11 : Nat).bits] : Fin 9 → List Bool)
    ⟨k.val-50,by omega⟩


private def expectedCommitWords (occupied bad : Bool) : Fin 65 → List Bool := fun k =>
  if h : k.val < 59 then expectedSecondWords occupied bad ⟨k.val,h⟩
  else if k=60 then (6 : Nat).bits else []

/-- Independently calculated 2^10 * 2^(11-1) mod 23 = 6, retaining every
previous word. This checks a typed endpoint; execution has a separate code gate. -/
theorem full_state_presentation (occupied bad : Bool) :
    PrimeSecondCommitMachine.sourceResult 0 g pk true (inputState occupied bad) live draws newScalars =
      (⟨none,2,expectedCommitWords occupied bad⟩ : PrimeSecondCommitMachine.Config) := by
  have hold : PrimeSecondCommitSource.words 0 g pk true (inputState occupied bad) live draws newScalars =
      expectedSecondWords occupied bad :=
    congrArg (fun cfg : PrimeSecondTranscriptMachine.Config => cfg.stk)
      (PrimeSecondTranscriptControls.full_state_presentation occupied bad)
  unfold PrimeSecondCommitMachine.sourceResult
  rw [hold]
  change (⟨_,_,_⟩ : PrimeSecondCommitMachine.Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

/-- The earlier first-proof coordinate 16 and stale e=0 coordinate 12 are
both different from the fresh second-proof coordinate 6. -/
theorem stale_commitment_and_scalar_excluded :
    let cfg := PrimeSecondCommitMachine.sourceResult 0 g pk true
      (inputState false false) live draws newScalars
    cfg.stk 60 = (6 : Nat).bits ∧ cfg.stk 60 ≠ cfg.stk 3 ∧
    cfg.stk 60 ≠ (12 : Nat).bits ∧ cfg.stk 55 ≠ cfg.stk 11 := by
  rw [full_state_presentation]
  decide +kernel

/-- Nonempty p0, updated saved state and original raw context survive unchanged. -/
theorem prior_proof_saved_and_context_retained (occupied bad : Bool) :
    let cfg := PrimeSecondCommitMachine.sourceResult 0 g pk true
      (inputState occupied bad) live draws newScalars
    cfg.stk 48 = proofWord ∧ cfg.stk 49 = savedWord occupied bad ∧
    cfg.stk 14 = rawWord occupied bad ∧ cfg.stk 46 = [bad || occupied] ∧
    cfg.stk 59 = [] ∧ cfg.stk 61 = [] ∧ cfg.stk 62 = [] ∧ cfg.stk 63 = [] ∧ cfg.stk 64 = [] := by
  rw [full_state_presentation]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Zero e is valid: the subgroup exponent representative is q=11, producing
2^10 mod 23 = 12. It is not canonical residue negation (which would be zero). -/
theorem zero_challenge_boundary :
    (PrimeSecondCommitMachine.sourceResult 0 g pk true (inputState false false) live draws
      (0,0,10,0)).stk 60 = (12 : Nat).bits ∧
    11-(0 : ZMod 11).val = 11 ∧ 11-(0 : ZMod 11).val ≠ (-(0 : ZMod 11)).val := by
  decide +kernel

#print axioms full_state_presentation
#print axioms stale_commitment_and_scalar_excluded
#print axioms prior_proof_saved_and_context_retained
#print axioms zero_challenge_boundary
end ExplainableCrypto.Helios.Computational.PrimeSecondCommitControls
