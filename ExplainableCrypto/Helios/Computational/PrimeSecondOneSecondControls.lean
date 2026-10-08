import ExplainableCrypto.Helios.Computational.PrimeSecondOneSecondMachineSource
import ExplainableCrypto.Helios.Computational.PrimeSecondOneFirstControls
import ExplainableCrypto.Helios.Computational.BallotStateCodecControls

namespace ExplainableCrypto.Helios.Computational.PrimeSecondOneSecondControls
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
/-- Independently computed d=10, gamma=2 and z1=0 yield coordinate 2.
Every prior word is checked against the literal encoded fixture. -/
theorem full_state_presentation (occupied bad : Bool) :
    PrimeSecondOneSecondMachine.sourceResult 0 g pk true (inputState occupied bad) live draws newScalars =
      (⟨none,2,expectedSecondOneWords occupied bad⟩ : PrimeSecondOneSecondMachine.Config) := by
  have hold : PrimeSecondOneSecondMachine.words 0 g pk true (inputState occupied bad) live draws newScalars =
      expectedFirstWords occupied bad :=
    (congrArg (fun cfg : PrimeSecondOneFirstMachine.Config => cfg.stk)
      (PrimeSecondOneFirstControls.full_state_presentation occupied bad)).trans (by
        funext k
        fin_cases k <;> rfl)
  unfold PrimeSecondOneSecondMachine.sourceResult
  rw [hold]
  change (⟨_,_,_⟩ : PrimeSecondOneSecondMachine.Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

/-- Actual execution, with independently fixed full-state output for all sticky/collision cases. -/
theorem execution_full_state (occupied bad : Bool) :
    ∃ charge ≤ PrimeSecondOneSecondMachine.cost 23 11,
      BitOracleMachine.run PrimeSecondOneSecondMachine.code (PrimeSecondOneSecondMachine.clock 23 11)
        (PrimeSecondOneSecondMachine.start (PrimeSecondOneFirstMachine.sourceResult 0 g pk true
          (inputState occupied bad) live draws newScalars).stk) =
      pure ((⟨none,2,expectedSecondOneWords occupied bad⟩ : PrimeSecondOneSecondMachine.Config),charge) := by
  obtain ⟨charge,hc,he⟩ := PrimeSecondOneSecondMachine.charged_source 0 g pk true (inputState occupied bad) live draws newScalars
  rw [full_state_presentation] at he
  exact ⟨charge,hc,he⟩

/-- Fresh d and z1 cannot be replaced by old e or the other response. -/
theorem stale_scalar_excluded :
    let cfg := PrimeSecondOneSecondMachine.sourceResult 0 g pk true (inputState false false) live draws newScalars
    cfg.stk 69 = (2 : Nat).bits ∧ cfg.stk 69 ≠ (12 : Nat).bits ∧
    cfg.stk 69 ≠ (1 : Nat).bits ∧ cfg.stk 66 = uniformNatEncode 10 ∧
    cfg.stk 55 = uniformNatEncode 1 ∧ cfg.stk 57 = uniformNatEncode 0 := by
  rw [full_state_presentation]
  decide +kernel

theorem prior_words_and_cleanup (occupied bad : Bool) :
    let cfg := PrimeSecondOneSecondMachine.sourceResult 0 g pk true (inputState occupied bad) live draws newScalars
    cfg.stk 48 = proofWord ∧ cfg.stk 49 = savedWord occupied bad ∧
    cfg.stk 14 = rawWord occupied bad ∧ cfg.stk 60 = (6 : Nat).bits ∧
    cfg.stk 65 = (13 : Nat).bits ∧ cfg.stk 59 = [] ∧ cfg.stk 61 = [] ∧
    cfg.stk 62 = [] ∧ cfg.stk 63 = [] ∧ cfg.stk 64 = [] := by
  rw [full_state_presentation]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Zero canonical d uses the subgroup exponent q and accepts the zero response. -/
theorem zero_difference :
    (PrimeSecondOneSecondMachine.sourceResult 0 g pk true (inputState false false) live draws (1,1,10,0)).stk 69 =
      (1 : Nat).bits ∧ 11-(0 : ZMod 11).val = 11 := by
  decide +kernel

/-- Modular underflow c=0,e=1 gives d=10; truncated subtraction would give the wrong result 1. -/
theorem underflow_not_truncated :
    let cfg := PrimeSecondOneSecondMachine.sourceResult 0 g pk true (inputState false false) live draws newScalars
    cfg.stk 66 = uniformNatEncode 10 ∧ cfg.stk 69 ≠ (1 : Nat).bits := by
  rw [full_state_presentation]
  decide +kernel

/-- The executed adjusted beta is 2, whereas reusing beta=4 gives the wrong coordinate 4. -/
theorem adjusted_gamma_not_beta :
    let cfg := PrimeSecondOneSecondMachine.sourceResult 0 g pk true
      (inputState false false) live draws newScalars
    cfg.stk 67 = (2 : Nat).bits ∧ cfg.stk 51 = (4 : Nat).bits ∧
    cfg.stk 69 = (2 : Nat).bits ∧ cfg.stk 69 ≠ (4 : Nat).bits := by
  rw [full_state_presentation]
  decide +kernel

private def corruptSavedProgram (l : Fin PrimeSecondOneSecondMachine.size) :=
  if l=12 then Turing.TM2.Stmt.push (49 : Fin 70) (fun _ => false) (PrimeSecondOneSecondMachine.program l)
  else PrimeSecondOneSecondMachine.program l

/-- An actual changed instruction corrupts the nonempty saved state at final return. -/
theorem actual_saved_corruption :
    (TM2ReturnLink.tick corruptSavedProgram
      (⟨some 12,0,expectedSecondOneWords false false⟩ : PrimeSecondOneSecondMachine.Config)).stk 49 =
        false :: savedWord false false ∧
    (TM2ReturnLink.tick corruptSavedProgram
      (⟨some 12,0,expectedSecondOneWords false false⟩ : PrimeSecondOneSecondMachine.Config)).stk 49 ≠
        savedWord false false := by
  decide +kernel

#print axioms zero_difference
#print axioms underflow_not_truncated
#print axioms adjusted_gamma_not_beta
#print axioms full_state_presentation
#print axioms execution_full_state
#print axioms stale_scalar_excluded
#print axioms prior_words_and_cleanup
#print axioms actual_saved_corruption
end ExplainableCrypto.Helios.Computational.PrimeSecondOneSecondControls
