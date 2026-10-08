import ExplainableCrypto.Helios.Computational.PrimeProgramMachineRun

/-! Reusable resident programming update for one typed statement/transcript.
The operational code is exactly PrimeProgramMachine.code. Every cache/history
and entry premise is derived from the current canonical records, independently
of old raw input. This does not yet execute a complete proof request. -/
namespace ExplainableCrypto.Helios.Computational.PrimeProgramRequestRun
open OracleComp OracleSpec BitOracleMachine
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
attribute [local irreducible] BitOracleMachine.run

abbrev State := BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q)
abbrev Cache := BallotFiniteCache (ZMod q) (PrimeGroup p q)
abbrev Transcript := BallotCommitment (PrimeGroup p q) × ZMod q × BallotResponse (ZMod q)

def inputWords (stmt : BallotStatement (PrimeGroup p q)) (tr : Transcript (p:=p) (q:=q))
    (state : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q))
    (frame : Fin 31 → List Bool) : Fin 48 → List Bool :=
  ![(primeGroupCoordinate stmt.ciphertext.2).val.bits,frame 0,frame 1,frame 2,
    frame 3,frame 4,frame 5,frame 6,frame 7,frame 8,scalarEncode tr.2.1,
    frame 9,frame 10,frame 11,frame 12,(primeGroupCoordinate stmt.publicKey).val.bits,
    (primeGroupCoordinate stmt.generator).val.bits,(primeGroupCoordinate stmt.ciphertext.1).val.bits,
    frame 13,frame 14,frame 15,frame 16,frame 17,[],[],[],[],[],[],[],
    frame 18,frame 19,frame 20,frame 21,frame 22,frame 23,frame 24,frame 25,
    frame 26,frame 27,frame 28,frame 29,frame 30,(ballotKeyBitCodec p q).encode (stmt,tr.1),
    (ballotCacheBitCodec p q).encode state.cache,(ballotCacheBitCodec p q).encode live,
    [state.bad],(ballotStatementBitCodec p q).list.encode state.programmed]

def framePorts : Fin 31 → Fin 48 :=
  ![1,2,3,4,5,6,7,8,9,11,12,13,14,18,19,20,21,22,30,31,32,33,34,35,36,37,38,39,40,41,42]

def inputSize (state : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) : Nat :=
  max ((ballotCacheBitCodec p q).encode state.cache).length
    (max ((ballotCacheBitCodec p q).encode live).length
      ((ballotStatementBitCodec p q).list.encode state.programmed).length)

def resultWords (stmt : BallotStatement (PrimeGroup p q)) (tr : Transcript (p:=p) (q:=q))
    (state : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q))
    (frame : Fin 31 → List Bool) : Fin 48 → List Bool :=
  let next := (state.program stmt tr).2
  Function.update (Function.update (Function.update (inputWords stmt tr state live frame)
    44 ((ballotCacheBitCodec p q).encode next.cache)) 46 [next.bad])
    47 ((ballotStatementBitCodec p q).list.encode next.programmed)

def result (stmt : BallotStatement (PrimeGroup p q)) (tr : Transcript (p:=p) (q:=q))
    (state : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q))
    (frame : Fin 31 → List Bool) : PrimeProgramMachine.Config :=
  ⟨none,2,resultWords stmt tr state live frame⟩

/-- A successful result is immediately the next canonical input for the same
statement/transcript; the current state is advanced and the arbitrary frame retained. -/
theorem result_next_input (stmt : BallotStatement (PrimeGroup p q)) (tr : Transcript (p:=p) (q:=q))
    (state : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (frame : Fin 31 → List Bool) :
    resultWords stmt tr state live frame = inputWords stmt tr (state.program stmt tr).2 live frame := by
  funext k
  fin_cases k <;> rfl

theorem result_retained (stmt : BallotStatement (PrimeGroup p q)) (tr : Transcript (p:=p) (q:=q))
    (state : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (frame : Fin 31 → List Bool)
    (k : Fin 31) : resultWords stmt tr state live frame (framePorts k) = frame k := by
  fin_cases k <;> rfl

theorem input_work (stmt : BallotStatement (PrimeGroup p q)) (tr : Transcript (p:=p) (q:=q))
    (state : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (frame : Fin 31 → List Bool)
    (j : Fin 7) : inputWords stmt tr state live frame ⟨23+j.val,by omega⟩ = [] := by
  fin_cases j <;> rfl

private theorem size_bounds (state : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) :
    ((ballotCacheBitCodec p q).encode state.cache).length ≤ inputSize state live ∧
    ((ballotCacheBitCodec p q).encode live).length ≤ inputSize state live ∧
    ((ballotStatementBitCodec p q).list.encode state.programmed).length ≤ inputSize state live :=
  ⟨Nat.le_max_left _ _,(Nat.le_max_left _ _).trans (Nat.le_max_right _ _),
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)⟩

private def insertedWords (stmt : BallotStatement (PrimeGroup p q)) (tr : Transcript (p:=p) (q:=q))
    (state : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (frame : Fin 31 → List Bool) :=
  Function.update (Function.update (inputWords stmt tr state live frame) 44
    ((ballotCacheBitCodec p q).encode
      (CacheProgrammedInsertMachine.programmedCache state.cache (stmt,tr.1) tr.2.1)))
    46 [state.bad || !(state.cache.lookup (stmt,tr.1)).isNone]

private theorem insert_charged (stmt : BallotStatement (PrimeGroup p q)) (tr : Transcript (p:=p) (q:=q))
    (state : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (saved : Fin 31 → List Bool) :
    ∃ charge ≤ PrimeProgrammedInsertMachine.cost p q (inputSize state live),
      BitOracleMachine.run PrimeProgrammedInsertMachine.code
        (PrimeProgrammedInsertMachine.clock p q (inputSize state live))
        (PrimeProgrammedInsertMachine.start (inputWords stmt tr state live saved)) =
      pure (⟨none,2,insertedWords stmt tr state live saved⟩,charge) := by
  let old := inputWords stmt tr state live saved
  let N := inputSize state live
  have hw (j : Fin 7) : old ⟨23+j.val,by omega⟩ = [] := input_work stmt tr state live saved j
  obtain ⟨hcache,hlive,hhistory⟩ := size_bounds state live
  have hn := (CacheHashHandler.entries_le state.cache).trans hcache
  have hI : CacheProgrammedInsertMachine.insertionFuel state.cache ≤
      PrimeProgrammedInsertMachine.insertBound p q N := CacheInsertMachine.cost_mono hn hcache
  have hk := ballotKeyBits_length_le (p:=p) (q:=q) (stmt,tr.1)
  have hv := scalarEncode_length_le tr.2.1
  have hH : CacheProgrammedInsertMachine.canonicalInputBound state.cache (stmt,tr.1) tr.2.1
      ((ballotCacheBitCodec p q).encode live)
      ((ballotStatementBitCodec p q).list.encode state.programmed) ≤
      PrimeProgrammedInsertMachine.inputBound p q N := by
    unfold CacheProgrammedInsertMachine.canonicalInputBound CacheProgrammedInsertMachine.inputBound PrimeProgrammedInsertMachine.inputBound
    dsimp only [N]
    change ((primeScalarBitCodec q).encode tr.2.1).length ≤ 2*(q-1).size+1 at hv
    change _ ≤ 1+3*inputSize state live+keyRecordBitBound p+(2*(q-1).size+1)
    omega
  have hc := CacheProgrammedInsertMachine.charged_bounded state.cache (stmt,tr.1) tr.2.1
    ((ballotCacheBitCodec p q).encode live)
    ((ballotStatementBitCodec p q).list.encode state.programmed) state.bad
    (PrimeProgrammedInsertMachine.insertBound p q N)
    (PrimeProgrammedInsertMachine.inputBound p q N) hI hH
  obtain ⟨charge,hcharge,he⟩ := PrimeProgrammedInsertMachine.charged_link old N
    (PrimeProgrammedInsertMachine.coreClock p q N)
    (CacheProgrammedInsertMachine.cost (PrimeProgrammedInsertMachine.insertBound p q N)
      (PrimeProgrammedInsertMachine.inputBound p q N))
    (hw 0) (hw 1) hcache _ _ (PrimeProgrammedInsertMachine.frame old)
    (PrimeProgrammedInsertMachine.prep_return old state.bad (fun j => hw ⟨j.val,by omega⟩) rfl) rfl hc
  have hout := PrimeProgrammedInsertMachine.core_result old
    ((ballotCacheBitCodec p q).encode (CacheProgrammedInsertMachine.programmedCache state.cache
      (stmt,tr.1) tr.2.1)) (state.bad || !(state.cache.lookup (stmt,tr.1)).isNone)
    (fun j => hw ⟨j.val,by omega⟩)
  refine ⟨charge,?_,he.trans (congrArg (fun cfg => pure (cfg,charge)) hout)⟩
  simpa only [PrimeProgrammedInsertMachine.cost,PrimeProgrammedInsertMachine.clock,
    PrimeProgrammedInsertMachine.prepareClock,PrimeProgrammedInsertMachine.coreClock,
    CacheProgrammedInsertMachine.cost,Nat.mul_add] using hcharge

private theorem program_fields (stmt : BallotStatement (PrimeGroup p q))
    (tr : Transcript (p:=p) (q:=q)) (state : State (p:=p) (q:=q)) :
    (state.program stmt tr).2.cache = CacheProgrammedInsertMachine.programmedCache state.cache (stmt,tr.1) tr.2.1 ∧
    (state.program stmt tr).2.bad = (state.bad || !(state.cache.lookup (stmt,tr.1)).isNone) ∧
    (state.program stmt tr).2.programmed = stmt :: state.programmed := by
  unfold BallotFiniteProgrammedState.program CacheProgrammedInsertMachine.programmedCache
  split <;> simp_all

private theorem history_charged (stmt : BallotStatement (PrimeGroup p q)) (tr : Transcript (p:=p) (q:=q))
    (state : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (saved : Fin 31 → List Bool) :
    ∃ charge ≤ PrimeProgrammedHistoryMachine.cost p (inputSize state live),
      BitOracleMachine.run PrimeProgrammedHistoryMachine.code
        (PrimeProgrammedHistoryMachine.clock p (inputSize state live))
        (PrimeProgrammedHistoryMachine.start (insertedWords stmt tr state live saved)) =
      pure (⟨none,2,resultWords stmt tr state live saved⟩,charge) := by
  let old := insertedWords stmt tr state live saved
  let elements : Fin 4 → PrimeGroup p q := ![stmt.ciphertext.2,stmt.ciphertext.1,stmt.publicKey,stmt.generator]
  let v : Fin 4 → Nat := fun i => (primeGroupCoordinate (elements i)).val
  let hs := state.programmed.map (ballotStatementBitCodec p q).encode
  have hw (j : Fin 7) : old ⟨23+j.val,by omega⟩ = [] := by fin_cases j <;> rfl
  have hv (i : Fin 4) : v i < p := (primeGroupCoordinate (elements i)).val_lt
  have hn (i : Fin 4) : old (PrimeProgrammedHistoryMachine.sourcePort i) = (v i).bits := by
    fin_cases i <;> rfl
  have hh : old 47 = bitFieldsEncode hs := rfl
  have hN : (old 47).length ≤ inputSize state live := (size_bounds state live).2.2
  have hstmt : PrimeProgrammedHistoryMachine.statement (v 3) (v 2) (v 1) (v 0) =
      (ballotStatementBitCodec p q).encode stmt := rfl
  obtain ⟨charge,hc,he⟩ := PrimeProgrammedHistoryMachine.charged_bounded p (inputSize state live)
    v hs old hw hv hn hh hN
  rw [hstmt] at he
  have hout : PrimeProgrammedHistoryMachine.result
      (bitFieldsEncode ((ballotStatementBitCodec p q).encode stmt :: hs)) old =
      (⟨none,2,resultWords stmt tr state live saved⟩ : PrimeProgrammedHistoryMachine.Config) := by
    obtain ⟨hcache,hbad,hhist⟩ := program_fields stmt tr state
    simp only [PrimeProgrammedHistoryMachine.result,resultWords,hcache,hbad,hhist]
    rfl
  exact ⟨charge,hc,he.trans (congrArg (fun cfg => pure (cfg,charge)) hout)⟩

/-- The unchanged resident program executes an arbitrary typed request. Its cost
is derived from the current cache/live/history record lengths; no old raw-input
or source-correspondence premise is required. -/
theorem charged (stmt : BallotStatement (PrimeGroup p q)) (tr : Transcript (p:=p) (q:=q))
    (state : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (saved : Fin 31 → List Bool) :
    ∃ charge ≤ PrimeProgramMachine.cost p q (inputSize state live),
      BitOracleMachine.run PrimeProgramMachine.code
        (PrimeProgramMachine.clock p q (inputSize state live))
        (PrimeProgramMachine.start (inputWords stmt tr state live saved)) =
      pure (result stmt tr state live saved,charge) := by
  let N := inputSize state live
  let initial := inputWords stmt tr state live saved
  let middle : PrimeProgrammedInsertMachine.Config := ⟨none,2,insertedWords stmt tr state live saved⟩
  obtain ⟨a,ha,hp⟩ := insert_charged stmt tr state live saved
  obtain ⟨b,hb,ht⟩ := history_charged stmt tr state live saved
  have boundary : BitOracleReturnLink.embed PrimeProgramMachine.prefixLabel
      (some (PrimeProgramMachine.tailLabel 0)) middle =
      BitOracleReturnLink.embed PrimeProgramMachine.tailLabel none
        (PrimeProgrammedHistoryMachine.start middle.stk) := rfl
  have tail : BitOracleMachine.run PrimeProgramMachine.code (PrimeProgrammedHistoryMachine.clock p N)
      (BitOracleReturnLink.embed PrimeProgramMachine.prefixLabel (some (PrimeProgramMachine.tailLabel 0)) middle) =
      pure (result stmt tr state live saved,b) := by
    rw [boundary,BitOracleReturnLink.rename_run _ _ _ PrimeProgramMachine.tail_code,ht,map_pure]
    rfl
  have hh : ∀ first ∈ support (BitOracleMachine.run PrimeProgrammedInsertMachine.code
      (PrimeProgrammedInsertMachine.clock p q N) (PrimeProgrammedInsertMachine.start initial)),
      first.1.l = none := by
    rw [hp]
    intro first hf
    rw [eq_of_mem_support_pure _ hf]
  have hc : ∀ first ∈ support (BitOracleMachine.run PrimeProgrammedInsertMachine.code
      (PrimeProgrammedInsertMachine.clock p q N) (PrimeProgrammedInsertMachine.start initial)),
      ∀ last ∈ support (BitOracleMachine.run PrimeProgramMachine.code (PrimeProgrammedHistoryMachine.clock p N)
        (BitOracleReturnLink.embed PrimeProgramMachine.prefixLabel (some (PrimeProgramMachine.tailLabel 0)) first.1)),
        last.1.l = none := by
    rw [hp]
    intro first hf
    rw [eq_of_mem_support_pure _ hf,tail]
    intro last hl
    rw [eq_of_mem_support_pure _ hl]
    rfl
  refine ⟨a+b,Nat.add_le_add ha hb,?_⟩
  change BitOracleMachine.run PrimeProgramMachine.code (_+_) (BitOracleReturnLink.embed PrimeProgramMachine.prefixLabel _ _) = _
  rw [BitOracleReturnLink.run _ _ _ _ PrimeProgramMachine.prefix_code _ _ _ hh hc,hp]
  simp only [pure_bind]
  change (do
    let last ← BitOracleMachine.run PrimeProgramMachine.code (PrimeProgrammedHistoryMachine.clock p N)
      (BitOracleReturnLink.embed PrimeProgramMachine.prefixLabel (some (PrimeProgramMachine.tailLabel 0)) middle)
    pure (last.1,a+last.2)) = _
  rw [tail,pure_bind]

/-- Re-enter the same executed program on the first result's actual words. This
is a two-invocation composition, with no new input serialization between calls. -/
theorem twice_charged (stmt : BallotStatement (PrimeGroup p q)) (tr : Transcript (p:=p) (q:=q))
    (state : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (saved : Fin 31 → List Bool) :
    let next := (state.program stmt tr).2
    ∃ charge ≤ PrimeProgramMachine.cost p q (inputSize state live) +
        PrimeProgramMachine.cost p q (inputSize next live),
      (do
        let first ← BitOracleMachine.run PrimeProgramMachine.code
          (PrimeProgramMachine.clock p q (inputSize state live))
          (PrimeProgramMachine.start (inputWords stmt tr state live saved))
        let second ← BitOracleMachine.run PrimeProgramMachine.code
          (PrimeProgramMachine.clock p q (inputSize next live))
          (PrimeProgramMachine.start first.1.stk)
        pure (second.1,first.2+second.2)) =
      pure (result stmt tr next live saved,charge) := by
  dsimp only
  obtain ⟨a,ha,he⟩ := charged stmt tr state live saved
  obtain ⟨b,hb,hf⟩ := charged stmt tr (state.program stmt tr).2 live saved
  refine ⟨a+b,Nat.add_le_add ha hb,?_⟩
  rw [he,pure_bind]
  change (do
    let second ← BitOracleMachine.run PrimeProgramMachine.code _
      (PrimeProgramMachine.start (resultWords stmt tr state live saved))
    pure (second.1,a+second.2)) = _
  rw [result_next_input,hf,pure_bind]

namespace Controls
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
private def coord (n : Nat) (h : (n : ZMod 3)^2=1) : PrimeGroup 3 2 :=
  Additive.ofMul (rootsOfUnity.mkOfPowEq (n : ZMod 3) h)
private def stmt : BallotStatement (PrimeGroup 3 2) :=
  ⟨coord 2 (by decide),coord 1 (by decide),coord 2 (by decide),coord 1 (by decide)⟩
private def tr : Transcript (p:=3) (q:=2) :=
  (((coord 1 (by decide),coord 1 (by decide)),(coord 1 (by decide),coord 1 (by decide))),0,(0,0,0))
private def initial (bad : Bool) : State (p:=3) (q:=2) := ⟨∅,bad,[]⟩
private def live : Cache (p:=3) (q:=2) := ∅
private def saved : Fin 31 → List Bool := fun _ => [true,false]
private def first (bad : Bool) := ((initial bad).program stmt tr).2
private def keyWord := bitFieldsEncode ([2,1,2,1,1,1,1,1].map uniformNatEncode)
private def stmtWord := bitFieldsEncode
  [bitFieldsEncode [uniformNatEncode 2,uniformNatEncode 1],
   bitFieldsEncode [uniformNatEncode 2,uniformNatEncode 1]]
private def cacheWord := bitFieldsEncode [bitFieldsEncode [keyWord,uniformNatEncode 0]]
private def expected (history : List (List Bool)) (bad : Bool) : Fin 48 → List Bool :=
  ![[true],[true,false],[true,false],[true,false],[true,false],[true,false],[true,false],
    [true,false],[true,false],[true,false],uniformNatEncode 0,[true,false],[true,false],
    [true,false],[true,false],[true],[false,true],[false,true],[true,false],[true,false],
    [true,false],[true,false],[true,false],[],[],[],[],[],[],[],[true,false],[true,false],
    [true,false],[true,false],[true,false],[true,false],[true,false],[true,false],
    [true,false],[true,false],[true,false],[true,false],[true,false],keyWord,
    cacheWord,bitFieldsEncode [],[bad],bitFieldsEncode history]

/-- Independently written complete numeric endpoint after a fresh insertion;
an initially true failure flag stays true. -/
theorem fresh_full_state (bad : Bool) : result stmt tr (initial bad) live saved =
    (⟨none,2,expected [stmtWord] bad⟩ : PrimeProgramMachine.Config) := by
  cases bad <;> change (⟨_,_,_⟩ : PrimeProgramMachine.Config) = ⟨_,_,_⟩
  all_goals congr 1; funext k; fin_cases k <;> decide +kernel

/-- The second agreeing request keeps one cache entry, sets failure, and records
a second copy of the statement. These expected records are literal codec data. -/
theorem twice_full_state (bad : Bool) : result stmt tr (first bad) live saved =
    (⟨none,2,expected [stmtWord,stmtWord] true⟩ : PrimeProgramMachine.Config) := by
  cases bad <;> change (⟨_,_,_⟩ : PrimeProgramMachine.Config) = ⟨_,_,_⟩
  all_goals congr 1; funext k; fin_cases k <;> decide +kernel

/-- Actual two-call execution uses the first returned words unchanged. The
second clock is justified by the updated state, including its longer history. -/
theorem twice_execution (bad : Bool) :
    ∃ charge ≤ PrimeProgramMachine.cost 3 2 (inputSize (initial bad) live) +
        PrimeProgramMachine.cost 3 2 (inputSize (first bad) live),
      (do
        let a ← BitOracleMachine.run PrimeProgramMachine.code
          (PrimeProgramMachine.clock 3 2 (inputSize (initial bad) live))
          (PrimeProgramMachine.start (inputWords stmt tr (initial bad) live saved))
        let b ← BitOracleMachine.run PrimeProgramMachine.code
          (PrimeProgramMachine.clock 3 2 (inputSize (first bad) live))
          (PrimeProgramMachine.start a.1.stk)
        pure (b.1,a.2+b.2)) =
      pure ((⟨none,2,expected [stmtWord,stmtWord] true⟩ : PrimeProgramMachine.Config),charge) := by
  obtain ⟨charge,hc,he⟩ := twice_charged stmt tr (initial bad) live saved
  exact ⟨charge,hc,he.trans (congrArg (fun cfg => pure (cfg,charge)) (twice_full_state bad))⟩

theorem agreeing_is_not_unflagged : (result stmt tr (first false) live saved).stk 46 ≠ [false] := by
  rw [twice_full_state]
  decide

theorem duplicate_is_not_deduplicated : (result stmt tr (first false) live saved).stk 47 ≠
    bitFieldsEncode [stmtWord] := by
  rw [twice_full_state]
  decide +kernel

theorem actual_storage_growth : (first false).cache.entries.length = 1 ∧
    (first false).programmed.length = 1 ∧ ((first false).program stmt tr).2.cache.entries.length = 1 ∧
    ((first false).program stmt tr).2.programmed.length = 2 ∧
    inputSize (initial false) live < inputSize (first false) live := by decide +kernel
end Controls

#print axioms result_next_input
#print axioms result_retained
#print axioms input_work
#print axioms charged
#print axioms twice_charged
#print axioms Controls.fresh_full_state
#print axioms Controls.twice_full_state
#print axioms Controls.twice_execution
#print axioms Controls.agreeing_is_not_unflagged
#print axioms Controls.duplicate_is_not_deduplicated
#print axioms Controls.actual_storage_growth
end ExplainableCrypto.Helios.Computational.PrimeProgramRequestRun
