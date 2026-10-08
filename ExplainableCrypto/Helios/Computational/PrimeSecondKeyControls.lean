import ExplainableCrypto.Helios.Computational.PrimeSecondKeyMachineSource
import ExplainableCrypto.Helios.Computational.PrimeSecondOneSecondControls
import ExplainableCrypto.Helios.Computational.BallotStateCodecControls

namespace ExplainableCrypto.Helios.Computational.PrimeSecondKeyControls
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

private def newScalars : ZMod 11 × ZMod 11 × ZMod 11 × ZMod 11 := (0,1,10,0)
/-- New values are independently computed from g=2,pk=4,r2=1 and message zero.
All old50 words use the already audited literal predecessor fixture. -/
private def expectedSecondWords (occupied bad : Bool) : Fin 59 → List Bool := fun k =>
  if h : k.val < 50 then expectedFullWords occupied bad ⟨k.val,h⟩
  else (![ (2 : Nat).bits,(4 : Nat).bits,(1 : Nat).bits,[false],
      uniformNatEncode 0,uniformNatEncode 1,uniformNatEncode 10,uniformNatEncode 0,(11 : Nat).bits] : Fin 9 → List Bool)
    ⟨k.val-50,by omega⟩


private def expectedAdjustedWords (occupied bad : Bool) : Fin 68 → List Bool := fun k =>
  if h : k.val < 59 then expectedSecondWords occupied bad ⟨k.val,h⟩
  else (![[],(6 : Nat).bits,[],[],[],[],(13 : Nat).bits,uniformNatEncode 10,(2 : Nat).bits] : Fin 9 → List Bool)
    ⟨k.val-59,by omega⟩
private def expectedFirstWords (occupied bad : Bool) : Fin 69 → List Bool := fun k =>
  if h : k.val < 68 then expectedAdjustedWords occupied bad ⟨k.val,h⟩ else (2 : Nat).bits
private def expectedSecondOneWords (occupied bad : Bool) : Fin 70 → List Bool := fun k =>
  if h : k.val < 69 then expectedFirstWords occupied bad ⟨k.val,h⟩ else (2 : Nat).bits

/-- Independent original flat eight-field key order: g,pk,alpha,beta,A,B,C,D. -/
private def key1Word : List Bool := bitFieldsEncode ([2,4,2,4,6,13,2,2].map uniformNatEncode)
private def expectedKeyWords (occupied bad : Bool) : Fin 71 → List Bool := fun k =>
  if h : k.val < 70 then expectedSecondOneWords occupied bad ⟨k.val,h⟩ else key1Word

theorem full_state_presentation (occupied bad : Bool) :
    PrimeSecondKeyMachine.sourceResult 0 g pk true (inputState occupied bad) live draws newScalars =
      (⟨none,2,expectedKeyWords occupied bad⟩ : PrimeSecondKeyMachine.Config) := by
  have hold : PrimeSecondKeyMachine.words 0 g pk true (inputState occupied bad) live draws newScalars =
      expectedSecondOneWords occupied bad :=
    (congrArg (fun cfg : PrimeSecondOneSecondMachine.Config => cfg.stk)
      (PrimeSecondOneSecondControls.full_state_presentation occupied bad)).trans (by
        funext k
        fin_cases k <;> rfl)
  unfold PrimeSecondKeyMachine.sourceResult
  rw [hold]
  change (⟨_,_,_⟩ : PrimeSecondKeyMachine.Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

/-- The actual serializer reaches an independently fixed complete key/state endpoint. -/
theorem execution_full_state (occupied bad : Bool) :
    ∃ charge ≤ PrimeSecondKeyMachine.cost 23,
      BitOracleMachine.run PrimeSecondKeyMachine.code (PrimeSecondKeyMachine.clock 23)
        (PrimeSecondKeyMachine.start (PrimeSecondAllCommitCaller.sourceResult 0 g pk true
          (inputState occupied bad) live draws newScalars).stk) =
      pure ((⟨none,2,expectedKeyWords occupied bad⟩ : PrimeSecondKeyMachine.Config),charge) := by
  obtain ⟨charge,hc,he⟩ := PrimeSecondKeyMachine.charged_source 0 g pk true (inputState occupied bad) live draws newScalars
  rw [full_state_presentation] at he
  exact ⟨charge,hc,he⟩

/-- This second key differs from the saved first key and from using first-proof alpha/A. -/
theorem stale_operands_excluded :
    let cfg := PrimeSecondKeyMachine.sourceResult 0 g pk true (inputState false false) live draws newScalars
    cfg.stk 70 = key1Word ∧ cfg.stk 70 ≠ cfg.stk 43 ∧
    cfg.stk 70 ≠ bitFieldsEncode ([2,4,8,4,6,13,2,2].map uniformNatEncode) ∧
    cfg.stk 70 ≠ bitFieldsEncode ([2,4,2,4,16,13,2,2].map uniformNatEncode) := by
  rw [full_state_presentation]
  decide +kernel

theorem flat_order_and_count :
    key1Word ≠ bitFieldsEncode ([2,4,2,4,13,6,2,2].map uniformNatEncode) ∧
    key1Word ≠ bitFieldsEncode ([2,4,2,4,6,13,2].map uniformNatEncode) ∧
    key1Word ≠ bitFieldsEncode
      [bitFieldsEncode ([2,4,2,4].map uniformNatEncode),
       bitFieldsEncode ([6,13,2,2].map uniformNatEncode)] := by
  decide +kernel

theorem retained_proof_state_and_cleanup (occupied bad : Bool) :
    let cfg := PrimeSecondKeyMachine.sourceResult 0 g pk true (inputState occupied bad) live draws newScalars
    cfg.stk 48 = proofWord ∧ cfg.stk 49 = savedWord occupied bad ∧
    cfg.stk 14 = rawWord occupied bad ∧ cfg.stk 46 = [bad || occupied] ∧
    cfg.stk 23 = [] ∧ cfg.stk 24 = [] ∧ cfg.stk 25 = [] ∧ cfg.stk 26 = [] ∧ cfg.stk 27 = [] := by
  rw [full_state_presentation]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

private def corruptSavedProgram (l : Fin PrimeSecondKeyMachine.size) :=
  if l=168 then Turing.TM2.Stmt.push (49 : Fin 71) (fun _ => false) (PrimeSecondKeyMachine.program l)
  else PrimeSecondKeyMachine.program l

theorem actual_saved_corruption :
    (TM2ReturnLink.tick corruptSavedProgram
      (⟨some 168,2,expectedKeyWords false false⟩ : PrimeSecondKeyMachine.Config)).stk 49 =
        false :: savedWord false false ∧
    (TM2ReturnLink.tick corruptSavedProgram
      (⟨some 168,2,expectedKeyWords false false⟩ : PrimeSecondKeyMachine.Config)).stk 49 ≠
        savedWord false false := by
  decide +kernel

#print axioms full_state_presentation
#print axioms execution_full_state
#print axioms stale_operands_excluded
#print axioms flat_order_and_count
#print axioms retained_proof_state_and_cleanup
#print axioms actual_saved_corruption
end ExplainableCrypto.Helios.Computational.PrimeSecondKeyControls
