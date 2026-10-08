import ExplainableCrypto.Helios.Computational.PrimeRequestDrawsSource
import ExplainableCrypto.Helios.Computational.PrimeCommitRequestRun
import ExplainableCrypto.Helios.Computational.PrimeProgramRequestRun
import ExplainableCrypto.Helios.Computational.PrimeProgramOutputMachineRun

/-! Structural interfaces for composing the existing proof-request stages.
The current cache, live cache and history remain resident across stages. -/
namespace ExplainableCrypto.Helios.Computational.PrimeProofRequest
open OracleComp OracleSpec BitOracleMachine
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
/-- Link the existing resident stages directly. The older complete raw caller
re-extracts saved state between key construction and programming, so it cannot
be reentered with current resident state without this explicit return routing. -/
abbrev drawSize := PrimeRequestDraws.size
abbrev commitSize := PrimeCommitRequest.size
abbrev programSize := PrimeProgramMachine.size
abbrev outputSize := PrimeProgramOutputMachine.size
abbrev size := drawSize+commitSize+programSize+outputSize
abbrev Config := BitOracleMachine.Config 50 size 3

def drawLayout : Fin 23 ⊕ Fin 27 ≃ Fin 50 := finSumFinEquiv
def residentLayout : Fin 48 ⊕ Fin 2 ≃ Fin 50 := finSumFinEquiv
def drawCode := BitOracleStackFrame.code drawLayout PrimeRequestDraws.code
def commitCode := BitOracleStackFrame.code residentLayout PrimeCommitRequest.code
def programCode := BitOracleStackFrame.code residentLayout PrimeProgramMachine.code

def drawLabel (l : Fin drawSize) : Fin size := ⟨l.val,by have := l.isLt; dsimp [size]; omega⟩
def commitLabel (l : Fin commitSize) : Fin size := ⟨drawSize+l.val,by have := l.isLt; dsimp [size]; omega⟩
def programLabel (l : Fin programSize) : Fin size := ⟨drawSize+commitSize+l.val,by have := l.isLt; dsimp [size]; omega⟩
def outputLabel (l : Fin outputSize) : Fin size := ⟨drawSize+commitSize+programSize+l.val,by have := l.isLt; dsimp [size]; omega⟩

def code (l : Fin size) : Command 50 size 3 :=
  if h : l.val < drawSize then
    BitOracleReturnLink.command drawLabel (some (commitLabel (PrimeCommitRequest.aLabel 0)))
      (drawCode ⟨l.val,h⟩)
  else if h' : l.val < drawSize+commitSize then
    BitOracleReturnLink.command commitLabel (some (programLabel 0))
      (commitCode ⟨l.val-drawSize,by change l.val-drawSize < commitSize; omega⟩)
  else if h'' : l.val < drawSize+commitSize+programSize then
    BitOracleReturnLink.command programLabel (some (outputLabel (PrimeProgramOutputMachine.natLabel 0 0)))
      (programCode ⟨l.val-(drawSize+commitSize),by change l.val-(drawSize+commitSize) < programSize; omega⟩)
  else BitOracleReturnLink.command outputLabel none
    (PrimeProgramOutputMachine.code ⟨l.val-(drawSize+commitSize+programSize),by have := l.isLt; change l.val < drawSize+commitSize+programSize+outputSize at this; change l.val-(drawSize+commitSize+programSize) < outputSize; omega⟩)

theorem draw_code (l : Fin drawSize) : code (drawLabel l) =
    BitOracleReturnLink.command drawLabel (some (commitLabel (PrimeCommitRequest.aLabel 0))) (drawCode l) := by
  have h : (drawLabel l).val < drawSize := l.isLt
  simp only [code,dif_pos h]
  rfl

theorem commit_code (l : Fin commitSize) : code (commitLabel l) =
    BitOracleReturnLink.command commitLabel (some (programLabel 0)) (commitCode l) := by
  have h : ¬ (commitLabel l).val < drawSize := by dsimp [commitLabel]; omega
  have h' : (commitLabel l).val < drawSize+commitSize := by have := l.isLt; dsimp [commitLabel]; omega
  simp only [code]
  rw [dif_neg h,dif_pos h']
  simp only [commitLabel,Nat.add_sub_cancel_left]

theorem program_code (l : Fin programSize) : code (programLabel l) =
    BitOracleReturnLink.command programLabel (some (outputLabel (PrimeProgramOutputMachine.natLabel 0 0))) (programCode l) := by
  have h : ¬ (programLabel l).val < drawSize := by dsimp [programLabel]; omega
  have h' : ¬ (programLabel l).val < drawSize+commitSize := by dsimp [programLabel]; omega
  have h'' : (programLabel l).val < drawSize+commitSize+programSize := by have := l.isLt; dsimp [programLabel]; omega
  simp only [code]
  rw [dif_neg h,dif_neg h',dif_pos h'']
  simp only [programLabel,Nat.add_sub_cancel_left]

theorem output_code (l : Fin outputSize) : code (outputLabel l) =
    BitOracleReturnLink.command outputLabel none (PrimeProgramOutputMachine.code l) := by
  have h : ¬ (outputLabel l).val < drawSize := by dsimp [outputLabel]; omega
  have h' : ¬ (outputLabel l).val < drawSize+commitSize := by dsimp [outputLabel]; omega
  have h'' : ¬ (outputLabel l).val < drawSize+commitSize+programSize := by dsimp [outputLabel]; omega
  simp only [code]
  rw [dif_neg h,dif_neg h',dif_neg h'']
  simp only [outputLabel,Nat.add_sub_cancel_left]

#print axioms draw_code
#print axioms commit_code
#print axioms program_code
#print axioms output_code

abbrev State := BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q)
abbrev Cache := BallotFiniteCache (ZMod q) (PrimeGroup p q)
abbrev Scalars := ZMod q × ZMod q × ZMod q × ZMod q

def transcript (stmt : BallotStatement (PrimeGroup p q)) (cs : Scalars (q:=q)) :=
  (ballotSimCommit stmt cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2),cs.1,
    (cs.2.1,cs.2.2.1,cs.2.2.2))

def context (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q))
    (saved : Fin 6 → List Bool) : Fin 10 → List Bool :=
  ![saved 0,saved 1,saved 2,saved 3,saved 4,saved 5,
    (ballotCacheBitCodec p q).encode s.cache,(ballotCacheBitCodec p q).encode live,
    [s.bad],(ballotStatementBitCodec p q).list.encode s.programmed]

def frame (stmt : BallotStatement (PrimeGroup p q)) (cs : Scalars (q:=q))
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (saved : Fin 6 → List Bool) :=
  fun k => (PrimeCommitRequest.result stmt cs (context s live saved)).stk
    (PrimeProgramRequestRun.framePorts k)

/-- The complete commitment result is literally the programming entry. No
semantic-realization-to-presentation implication is used. -/
theorem commit_program_boundary (stmt : BallotStatement (PrimeGroup p q)) (cs : Scalars (q:=q))
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (saved : Fin 6 → List Bool) :
    (PrimeCommitRequest.result stmt cs (context s live saved)).stk =
      PrimeProgramRequestRun.inputWords stmt (transcript stmt cs) s live (frame stmt cs s live saved) := by
  funext k
  fin_cases k <;> rfl

def next (stmt : BallotStatement (PrimeGroup p q)) (cs : Scalars (q:=q))
    (s : State (p:=p) (q:=q)) : State (p:=p) (q:=q) :=
  (s.program stmt (transcript stmt cs)).2

def programmedWords (stmt : BallotStatement (PrimeGroup p q)) (cs : Scalars (q:=q))
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (saved : Fin 6 → List Bool) :=
  PrimeProgramRequestRun.resultWords stmt (transcript stmt cs) s live (frame stmt cs s live saved)

/-- Four natural-number fields occur in the order used by the existing writer. -/
def values (stmt : BallotStatement (PrimeGroup p q)) (cs : Scalars (q:=q)) : Fin 4 → Nat :=
  let com := (transcript stmt cs).1
  ![(primeGroupCoordinate com.1.2).val,(primeGroupCoordinate com.1.1).val,
    (primeGroupCoordinate com.2.2).val,(primeGroupCoordinate com.2.1).val]

theorem output_work (stmt : BallotStatement (PrimeGroup p q)) (cs : Scalars (q:=q))
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (saved : Fin 6 → List Bool)
    (j : Fin 15) : programmedWords stmt cs s live saved ⟨23+j.val,by omega⟩ = [] := by
  fin_cases j <;> rfl

theorem output_nats (stmt : BallotStatement (PrimeGroup p q)) (cs : Scalars (q:=q))
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (saved : Fin 6 → List Bool)
    (i : Fin 4) : programmedWords stmt cs s live saved (PrimeProgramOutputMachine.natOldSource i) =
      (values stmt cs i).bits := by
  fin_cases i <;> rfl

theorem output_scalars (stmt : BallotStatement (PrimeGroup p q)) (cs : Scalars (q:=q))
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (saved : Fin 6 → List Bool)
    (i : Fin 4) :
    (programmedWords stmt cs s live saved (PrimeProgramOutputMachine.scalarOldSource i)).length ≤
      groupRecordBitBound q := by
  fin_cases i <;> exact scalarEncode_length_le _

theorem output_proof (stmt : BallotStatement (PrimeGroup p q)) (cs : Scalars (q:=q))
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (saved : Fin 6 → List Bool) :
    PrimeProgramOutputMachine.proofEncoded (values stmt cs) (programmedWords stmt cs s live saved) =
      (ballotProofBitCodec p q).encode
        (ballotTranscriptProof (transcript stmt cs).1 cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2)) := rfl

theorem output_saved (stmt : BallotStatement (PrimeGroup p q)) (cs : Scalars (q:=q))
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (saved : Fin 6 → List Bool) :
    PrimeProgramOutputMachine.savedEncoded (programmedWords stmt cs s live saved) =
      (ballotBothCachesBitCodec p q).encode (next stmt cs s,live) := rfl

/-- Writer bounds depend on the current state, not an earlier serialized input. -/
def outputBound (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) :=
  max s.cache.entries.length (max s.programmed.length ((ballotCacheBitCodec p q).encode live).length)

omit [Fact (Nat.Prime p)] in
theorem next_counts (stmt : BallotStatement (PrimeGroup p q)) (cs : Scalars (q:=q))
    (s : State (p:=p) (q:=q)) :
    (next stmt cs s).cache.entries.length ≤ s.cache.entries.length+1 ∧
    (next stmt cs s).programmed.length = s.programmed.length+1 := by
  cases h : s.cache.lookup (stmt,(transcript stmt cs).1) with
  | some old => simp [next,BallotFiniteProgrammedState.program,h]
  | none =>
    have hn : (stmt,(transcript stmt cs).1) ∉ s.cache := by
      intro hk
      have he := AList.lookup_isSome.mpr hk
      simp [h] at he
    simp only [next,BallotFiniteProgrammedState.program,h]
    rw [AList.entries_insert_of_notMem hn]
    exact ⟨le_rfl,rfl⟩

def result (stmt : BallotStatement (PrimeGroup p q)) (cs : Scalars (q:=q))
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (saved : Fin 6 → List Bool) :=
  PrimeProgramOutputMachine.result
    ((ballotProofBitCodec p q).encode
      (ballotTranscriptProof (transcript stmt cs).1 cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2)))
    ((ballotBothCachesBitCodec p q).encode (next stmt cs s,live))
    (programmedWords stmt cs s live saved)

/-- All entry and size conditions of the existing proof/state encoder follow
from the composed commitment and programming result. -/
theorem output_charged (stmt : BallotStatement (PrimeGroup p q)) (cs : Scalars (q:=q))
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (saved : Fin 6 → List Bool) :
    ∃ charge ≤ PrimeProgramOutputMachine.cost p q (outputBound s live),
      BitOracleMachine.run PrimeProgramOutputMachine.code
        (PrimeProgramOutputMachine.clock p q (outputBound s live))
        (PrimeProgramOutputMachine.start (programmedWords stmt cs s live saved)) =
      pure (result stmt cs s live saved,charge) := by
  let old := programmedWords stmt cs s live saved
  let N := outputBound s live
  have hc : s.cache.entries.length ≤ N := Nat.le_max_left _ _
  have hh : s.programmed.length ≤ N := (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hl : ((ballotCacheBitCodec p q).encode live).length ≤ N :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  obtain ⟨hnc,hnh⟩ := next_counts stmt cs s
  have hs : (old 44).length ≤ PrimeProgramOutputMachine.shadowBound p q N :=
    ballotCacheBits_length_le_of_entries _ _ (hnc.trans (Nat.add_le_add_right hc 1))
  have ht : (old 47).length ≤ PrimeProgramOutputMachine.historyBound p N :=
    BitRecordCodec.list_length_le _ _ _ _ (fun st _ => ballotStatementBits_length_le st)
      (hnh.le.trans (Nat.add_le_add_right hh 1))
  have hv (i : Fin 4) : values stmt cs i < p := by
    fin_cases i <;> exact ZMod.val_lt _
  obtain ⟨charge,hcharge,he⟩ := PrimeProgramOutputMachine.charged p q N
    (values stmt cs) old (output_work stmt cs s live saved) hv
    (output_nats stmt cs s live saved) (output_scalars stmt cs s live saved) hs ht hl (by rfl)
  rw [output_proof,output_saved] at he
  exact ⟨charge,hcharge,he⟩

def statement (g pk : PrimeGroup p q) (vote : Bool) (r : ZMod q) : BallotStatement (PrimeGroup p q) :=
  ⟨g,pk,encryptWith g pk r (voteScalar vote)⟩

def retained (slack : Nat) (vote : Bool) (r : ZMod q) (second extra : List Bool) : Fin 6 → List Bool :=
  ![r.val.bits,extra,[vote],SamplerOperands.input slack q [],scalarEncode r,second]

def drawFrame (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) : Fin 27 → List Bool :=
  fun j => if j = 21 then (ballotCacheBitCodec p q).encode s.cache
    else if j = 22 then (ballotCacheBitCodec p q).encode live
    else if j = 23 then [s.bad]
    else if j = 24 then (ballotStatementBitCodec p q).list.encode s.programmed
    else []

def start (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (r : ZMod q)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (second extra : List Bool) : Config :=
  BitOracleReturnLink.embed drawLabel (some (commitLabel (PrimeCommitRequest.aLabel 0)))
    (BitOracleStackFrame.embed drawLayout (PrimeRequestDraws.sourceStart slack g pk vote r second extra)
      (drawFrame s live))

def fullResult (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (r : ZMod q)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (second extra : List Bool)
    (cs : Scalars (q:=q)) : Config :=
  BitOracleReturnLink.embed outputLabel none
    (result (statement g pk vote r) cs s live (retained slack vote r second extra))

def tailClock (p q : Nat) (inputN outputN : Nat) := PrimeCommitRequest.clock p q+
  (PrimeProgramMachine.clock p q inputN+PrimeProgramOutputMachine.clock p q outputN)
def tailCost (p q : Nat) (inputN outputN : Nat) := PrimeCommitRequest.cost p q+
  (PrimeProgramMachine.cost p q inputN+PrimeProgramOutputMachine.cost p q outputN)
def clock (slack : Nat) (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) :=
  PrimeRequestDraws.clock slack p q + tailClock p q (PrimeProgramRequestRun.inputSize s live) (outputBound s live)
def cost (slack : Nat) (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) :=
  PrimeRequestDraws.cost slack p q + tailCost p q (PrimeProgramRequestRun.inputSize s live) (outputBound s live)

/-- The draw output supplies the actual commitment entry, preserving current
resident state. The proof is an equality of all fifty words and the return label. -/
theorem draw_commit_boundary (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (r : ZMod q)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (second extra : List Bool)
    (cs : Scalars (q:=q)) :
    BitOracleReturnLink.embed drawLabel (some (commitLabel (PrimeCommitRequest.aLabel 0)))
      (BitOracleStackFrame.embed drawLayout (PrimeRequestDraws.sourceResult slack g pk vote r second extra cs)
        (drawFrame s live)) =
    BitOracleReturnLink.embed commitLabel (some (programLabel 0))
      (BitOracleStackFrame.embed residentLayout
        (PrimeCommitRequest.start (PrimeCommitRequest.inputWords (statement g pk vote r) cs
          (context s live (retained slack vote r second extra)))) (fun _ => [])) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

#print axioms draw_commit_boundary

/-- The actual successor supplies a bound for the next request's writer. -/
theorem next_outputBound (stmt : BallotStatement (PrimeGroup p q)) (cs : Scalars (q:=q))
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) :
    outputBound (next stmt cs s) live ≤ outputBound s live+1 := by
  obtain ⟨hc,hh⟩ := next_counts stmt cs s
  unfold outputBound
  omega

/-- The next programming-input size is derived from the actual update and
canonical codecs, with no old raw record or caller-supplied size certificate. -/
theorem next_inputSize (stmt : BallotStatement (PrimeGroup p q)) (cs : Scalars (q:=q))
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) :
    PrimeProgramRequestRun.inputSize (next stmt cs s) live ≤
      max (cacheRecordBitBound p q (outputBound s live+1))
        (max (outputBound s live) (bitListSize (statementRecordBitBound p) (outputBound s live+1))) := by
  obtain ⟨hc,hh⟩ := next_counts stmt cs s
  have hcache : s.cache.entries.length ≤ outputBound s live := Nat.le_max_left _ _
  have hhistory : s.programmed.length ≤ outputBound s live :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hlive : ((ballotCacheBitCodec p q).encode live).length ≤ outputBound s live :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  exact max_le_max (ballotCacheBits_length_le_of_entries _ _ (hc.trans (Nat.add_le_add_right hcache 1)))
    (max_le_max hlive (BitRecordCodec.list_length_le _ _ _ _
      (fun st _ => ballotStatementBits_length_le st) (hh.le.trans (Nat.add_le_add_right hhistory 1))))

omit [Fact (Nat.Prime p)] in
theorem program_return (stmt : BallotStatement (PrimeGroup p q)) (cs : Scalars (q:=q))
    (s : State (p:=p) (q:=q)) :
    (s.program stmt (transcript stmt cs)).1 =
      ballotTranscriptProof (transcript stmt cs).1 cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2) := by
  unfold BallotFiniteProgrammedState.program
  split <;> rfl

/-- Both returned encodings describe the same original source programming call. -/
theorem fullResult_return (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (r : ZMod q)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (second extra : List Bool)
    (cs : Scalars (q:=q)) :
    let op := s.program (statement g pk vote r) (transcript (statement g pk vote r) cs)
    let out := fullResult slack g pk vote r s live second extra cs
    out.stk 48 = (ballotProofBitCodec p q).encode op.1 ∧
    out.stk 49 = (ballotBothCachesBitCodec p q).encode (op.2,live) := by
  dsimp only
  rw [program_return]
  exact ⟨rfl,rfl⟩

#print axioms next_outputBound
#print axioms next_inputSize
#print axioms fullResult_return

attribute [local irreducible] BitOracleMachine.run
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

def linkedResult (stmt : BallotStatement (PrimeGroup p q)) (cs : Scalars (q:=q))
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (saved : Fin 6 → List Bool) : Config :=
  BitOracleReturnLink.embed outputLabel none (result stmt cs s live saved)

private theorem program_output_charged (stmt : BallotStatement (PrimeGroup p q)) (cs : Scalars (q:=q))
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (saved : Fin 6 → List Bool) :
    ∃ charge ≤ PrimeProgramMachine.cost p q (PrimeProgramRequestRun.inputSize s live)+
        PrimeProgramOutputMachine.cost p q (outputBound s live),
      BitOracleMachine.run code
        (PrimeProgramMachine.clock p q (PrimeProgramRequestRun.inputSize s live)+
          PrimeProgramOutputMachine.clock p q (outputBound s live))
        (BitOracleReturnLink.embed programLabel (some (outputLabel (PrimeProgramOutputMachine.natLabel 0 0)))
          (BitOracleStackFrame.embed residentLayout
            (PrimeProgramMachine.start (PrimeProgramRequestRun.inputWords stmt (transcript stmt cs) s live
              (frame stmt cs s live saved))) (fun _ => []))) =
      pure (linkedResult stmt cs s live saved,charge) := by
  obtain ⟨a,ha,he⟩ := PrimeProgramRequestRun.charged stmt (transcript stmt cs) s live (frame stmt cs s live saved)
  obtain ⟨b,hb,hf⟩ := output_charged stmt cs s live saved
  let initial := BitOracleStackFrame.embed residentLayout
    (PrimeProgramMachine.start (PrimeProgramRequestRun.inputWords stmt (transcript stmt cs) s live
      (frame stmt cs s live saved))) (fun _ => [])
  let finished := BitOracleStackFrame.embed residentLayout
    (PrimeProgramRequestRun.result stmt (transcript stmt cs) s live (frame stmt cs s live saved))
      (fun _ => [])
  have hp : BitOracleMachine.run programCode
      (PrimeProgramMachine.clock p q (PrimeProgramRequestRun.inputSize s live)) initial = pure (finished,a) := by
    dsimp only [programCode,initial]
    rw [BitOracleStackFrame.run,he,map_pure]
  have boundary : BitOracleReturnLink.embed programLabel
      (some (outputLabel (PrimeProgramOutputMachine.natLabel 0 0))) finished =
      BitOracleReturnLink.embed outputLabel none (PrimeProgramOutputMachine.start (programmedWords stmt cs s live saved)) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    funext k
    fin_cases k <;> rfl
  have tail : BitOracleMachine.run code (PrimeProgramOutputMachine.clock p q (outputBound s live))
      (BitOracleReturnLink.embed programLabel (some (outputLabel (PrimeProgramOutputMachine.natLabel 0 0))) finished) =
      pure (linkedResult stmt cs s live saved,b) := by
    rw [boundary,BitOracleReturnLink.rename_run _ _ _ output_code,hf,map_pure]
    rfl
  have hh : ∀ first ∈ support (BitOracleMachine.run programCode
      (PrimeProgramMachine.clock p q (PrimeProgramRequestRun.inputSize s live)) initial), first.1.l = none := by
    rw [hp]
    intro first h
    obtain rfl := eq_of_mem_support_pure _ h
    rfl
  have hc : ∀ first ∈ support (BitOracleMachine.run programCode
      (PrimeProgramMachine.clock p q (PrimeProgramRequestRun.inputSize s live)) initial),
      ∀ last ∈ support (BitOracleMachine.run code (PrimeProgramOutputMachine.clock p q (outputBound s live))
        (BitOracleReturnLink.embed programLabel (some (outputLabel (PrimeProgramOutputMachine.natLabel 0 0))) first.1)),
      last.1.l = none := by
    rw [hp]
    intro first h
    obtain rfl := eq_of_mem_support_pure _ h
    rw [tail]
    intro last h
    obtain rfl := eq_of_mem_support_pure _ h
    rfl
  refine ⟨a+b,Nat.add_le_add ha hb,?_⟩
  change BitOracleMachine.run code (_+_) (BitOracleReturnLink.embed programLabel _ initial) = _
  rw [BitOracleReturnLink.run _ _ _ _ program_code _ _ _ hh hc,hp,pure_bind,tail,pure_bind]

private theorem scalar_word_source (slack : Nat) :
    (fun bits => (bitsValue bits : ZMod q)) <$> CoinWordLoader.word (q.size+slack) =
      simulateQ CoinWordLoader.liftCoins (runFairBitUniform slack (uniformSample (ZMod q))) := by
  rw [PrimeFullFieldSource.uniform_zmod]
  have h := congrArg (fun oa : OracleComp BitOracleMachine.spec Nat =>
    (fun n : Nat => (n : ZMod q)) <$> oa) (CoinWordLoader.word_index (q.size+slack))
  simp only [Functor.map_map,simulateQ_map] at h ⊢
  rw [h]
  simp only [sampleFairBitRange,sampleFairBitModulo,simulateQ_map,Functor.map_map]
  congr 1
  funext a
  have hv : (ZMod.finEquiv q) ⟨a.val%q,Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q))⟩ =
      (a.val : ZMod q) := by
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q => rfl
  exact hv.symm


theorem tail_charged (stmt : BallotStatement (PrimeGroup p q)) (cs : Scalars (q:=q))
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (saved : Fin 6 → List Bool) :
    ∃ charge ≤ tailCost p q (PrimeProgramRequestRun.inputSize s live) (outputBound s live),
      BitOracleMachine.run code (tailClock p q (PrimeProgramRequestRun.inputSize s live) (outputBound s live))
        (BitOracleReturnLink.embed commitLabel (some (programLabel 0))
          (BitOracleStackFrame.embed residentLayout
            (PrimeCommitRequest.start (PrimeCommitRequest.inputWords stmt cs (context s live saved))) (fun _ => []))) =
      pure (linkedResult stmt cs s live saved,charge) := by
  obtain ⟨a,ha,he⟩ := PrimeCommitRequest.charged stmt cs (context s live saved)
  obtain ⟨b,hb,hf⟩ := program_output_charged stmt cs s live saved
  let initial := BitOracleStackFrame.embed residentLayout
    (PrimeCommitRequest.start (PrimeCommitRequest.inputWords stmt cs (context s live saved))) (fun _ => [])
  let finished := BitOracleStackFrame.embed residentLayout
    (PrimeCommitRequest.result stmt cs (context s live saved)) (fun _ => [])
  have hp : BitOracleMachine.run commitCode (PrimeCommitRequest.clock p q) initial = pure (finished,a) := by
    dsimp only [commitCode,initial]
    rw [BitOracleStackFrame.run,he,map_pure]
  have boundary : BitOracleReturnLink.embed commitLabel (some (programLabel 0)) finished =
      BitOracleReturnLink.embed programLabel (some (outputLabel (PrimeProgramOutputMachine.natLabel 0 0)))
        (BitOracleStackFrame.embed residentLayout
          (PrimeProgramMachine.start (PrimeProgramRequestRun.inputWords stmt (transcript stmt cs) s live
            (frame stmt cs s live saved))) (fun _ => [])) := by
    have h := commit_program_boundary stmt cs s live saved
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    change TM2StackFrame.data residentLayout _ _ = TM2StackFrame.data residentLayout _ _
    rw [h]
    rfl
  have tail : BitOracleMachine.run code
      (PrimeProgramMachine.clock p q (PrimeProgramRequestRun.inputSize s live)+
        PrimeProgramOutputMachine.clock p q (outputBound s live))
      (BitOracleReturnLink.embed commitLabel (some (programLabel 0)) finished) =
      pure (linkedResult stmt cs s live saved,b) := by rw [boundary]; exact hf
  have hh : ∀ first ∈ support (BitOracleMachine.run commitCode (PrimeCommitRequest.clock p q) initial),
      first.1.l = none := by
    rw [hp]
    intro first h
    obtain rfl := eq_of_mem_support_pure _ h
    rfl
  have hc : ∀ first ∈ support (BitOracleMachine.run commitCode (PrimeCommitRequest.clock p q) initial),
      ∀ last ∈ support (BitOracleMachine.run code
        (PrimeProgramMachine.clock p q (PrimeProgramRequestRun.inputSize s live)+
          PrimeProgramOutputMachine.clock p q (outputBound s live))
        (BitOracleReturnLink.embed commitLabel (some (programLabel 0)) first.1)), last.1.l = none := by
    rw [hp]
    intro first h
    obtain rfl := eq_of_mem_support_pure _ h
    rw [tail]
    intro last h
    obtain rfl := eq_of_mem_support_pure _ h
    rfl
  refine ⟨a+b,Nat.add_le_add ha hb,?_⟩
  change BitOracleMachine.run code (_+_) (BitOracleReturnLink.embed commitLabel _ initial) = _
  rw [BitOracleReturnLink.run _ _ _ _ commit_code _ _ _ hh hc,hp,pure_bind,tail,pure_bind]

#print axioms tail_charged

/-- One uninterrupted finite execution implements a complete programmed proof
request, including fresh transcript draws and the original returned proof/state. -/
theorem charged (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (r : ZMod q)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (second extra : List Bool) :
    ∃ charge : List Bool → List Bool → List Bool → List Bool → Nat,
      (∀ a, a.length=q.size+slack → ∀ b, b.length=q.size+slack →
        ∀ c, c.length=q.size+slack → ∀ d, d.length=q.size+slack → charge a b c d ≤ cost slack s live) ∧
      BitOracleMachine.run code (clock slack s live) (start slack g pk vote r s live second extra) = (do
        let a ← CoinWordLoader.word (q.size+slack)
        let b ← CoinWordLoader.word (q.size+slack)
        let c ← CoinWordLoader.word (q.size+slack)
        let d ← CoinWordLoader.word (q.size+slack)
        pure (fullResult slack g pk vote r s live second extra
          ((bitsValue a : ZMod q),(bitsValue b : ZMod q),(bitsValue c : ZMod q),(bitsValue d : ZMod q)),
          charge a b c d)) := by
  classical
  obtain ⟨a,ha,he⟩ := PrimeRequestDraws.charged_source slack g pk vote r second extra
  choose b hb ht using (fun cs : Scalars (q:=q) =>
    tail_charged (statement g pk vote r) cs s live (retained slack vote r second extra))
  let initial := BitOracleStackFrame.embed drawLayout
    (PrimeRequestDraws.sourceStart slack g pk vote r second extra) (drawFrame s live)
  let drawn := fun cs : Scalars (q:=q) => BitOracleStackFrame.embed drawLayout
    (PrimeRequestDraws.sourceResult slack g pk vote r second extra cs) (drawFrame s live)
  have hdraw : BitOracleMachine.run drawCode (PrimeRequestDraws.clock slack p q) initial = (do
      let c ← CoinWordLoader.word (q.size+slack)
      let e ← CoinWordLoader.word (q.size+slack)
      let z0 ← CoinWordLoader.word (q.size+slack)
      let z1 ← CoinWordLoader.word (q.size+slack)
      pure (drawn ((bitsValue c : ZMod q),(bitsValue e : ZMod q),(bitsValue z0 : ZMod q),(bitsValue z1 : ZMod q)),a c e z0 z1)) := by
    dsimp only [drawCode,initial]
    rw [BitOracleStackFrame.run,he]
    simp only [map_bind,map_pure]
    rfl
  have tail (cs : Scalars (q:=q)) : BitOracleMachine.run code
      (tailClock p q (PrimeProgramRequestRun.inputSize s live) (outputBound s live))
      (BitOracleReturnLink.embed drawLabel (some (commitLabel (PrimeCommitRequest.aLabel 0))) (drawn cs)) =
      pure (fullResult slack g pk vote r s live second extra cs,b cs) := by
    dsimp only [drawn]
    rw [draw_commit_boundary]
    exact ht cs
  have hh : ∀ first ∈ support (BitOracleMachine.run drawCode (PrimeRequestDraws.clock slack p q) initial),
      first.1.l = none := by
    rw [hdraw]
    intro first h
    rw [mem_support_bind_iff] at h; obtain ⟨c,_,h⟩ := h
    rw [mem_support_bind_iff] at h; obtain ⟨e,_,h⟩ := h
    rw [mem_support_bind_iff] at h; obtain ⟨z0,_,h⟩ := h
    rw [mem_support_bind_iff] at h; obtain ⟨z1,_,h⟩ := h
    obtain rfl := eq_of_mem_support_pure _ h
    rfl
  have hc : ∀ first ∈ support (BitOracleMachine.run drawCode (PrimeRequestDraws.clock slack p q) initial),
      ∀ last ∈ support (BitOracleMachine.run code
        (tailClock p q (PrimeProgramRequestRun.inputSize s live) (outputBound s live))
        (BitOracleReturnLink.embed drawLabel (some (commitLabel (PrimeCommitRequest.aLabel 0))) first.1)),
        last.1.l = none := by
    rw [hdraw]
    intro first h
    rw [mem_support_bind_iff] at h; obtain ⟨c,_,h⟩ := h
    rw [mem_support_bind_iff] at h; obtain ⟨e,_,h⟩ := h
    rw [mem_support_bind_iff] at h; obtain ⟨z0,_,h⟩ := h
    rw [mem_support_bind_iff] at h; obtain ⟨z1,_,h⟩ := h
    obtain rfl := eq_of_mem_support_pure _ h
    rw [tail]
    intro last h
    obtain rfl := eq_of_mem_support_pure _ h
    rfl
  refine ⟨fun c e z0 z1 => a c e z0 z1+
    b ((bitsValue c : ZMod q),(bitsValue e : ZMod q),(bitsValue z0 : ZMod q),(bitsValue z1 : ZMod q)),?_,?_⟩
  · intro c hc e he z0 hz0 z1 hz1
    exact Nat.add_le_add (ha c hc e he z0 hz0 z1 hz1) (hb _)
  · change BitOracleMachine.run code (_+_) (BitOracleReturnLink.embed drawLabel _ initial) = _
    rw [BitOracleReturnLink.run _ _ _ _ draw_code _ _ _ hh hc,hdraw]
    simp only [bind_assoc,pure_bind,tail]

#print axioms charged

/-- Exact fair-coin query-tree correspondence for the complete request. -/
theorem execution_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (r : ZMod q)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (second extra : List Bool) :
    Prod.fst <$> BitOracleMachine.run code (clock slack s live) (start slack g pk vote r s live second extra) =
      simulateQ CoinWordLoader.liftCoins
        (fullResult slack g pk vote r s live second extra <$>
          runFairBitUniform slack (PrimeFullFieldSource.drawTranscriptScalars q)) := by
  obtain ⟨charge,_,he⟩ := charged slack g pk vote r s live second extra
  rw [he]
  let W := (fun bits => (bitsValue bits : ZMod q)) <$> CoinWordLoader.word (q.size+slack)
  have hW := scalar_word_source (q:=q) slack
  change W = _ at hW
  calc
    _ = (do
      let a ← W
      let b ← W
      let c ← W
      let d ← W
      pure (fullResult slack g pk vote r s live second extra (a,b,c,d))) := by
      simp only [W,map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
    _ = _ := by
      rw [hW]
      simp only [PrimeFullFieldSource.drawTranscriptScalars,runFairBitUniform,simulateQ_bind,
        simulateQ_pure,map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]

theorem run_support (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (r : ZMod q)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (second extra : List Bool) :
    ∀ last ∈ support (BitOracleMachine.run code (clock slack s live) (start slack g pk vote r s live second extra)),
      last.1.l = none ∧ last.2 ≤ cost slack s live := by
  obtain ⟨charge,hc,he⟩ := charged slack g pk vote r s live second extra
  rw [he]
  intro last h
  rw [mem_support_bind_iff] at h; obtain ⟨a,ha,h⟩ := h
  rw [mem_support_bind_iff] at h; obtain ⟨b,hb,h⟩ := h
  rw [mem_support_bind_iff] at h; obtain ⟨c,hc',h⟩ := h
  rw [mem_support_bind_iff] at h; obtain ⟨d,hd,h⟩ := h
  obtain rfl := eq_of_mem_support_pure _ h
  exact ⟨rfl,hc a (CoinWordLoader.word_length _ _ ha) b (CoinWordLoader.word_length _ _ hb)
    c (CoinWordLoader.word_length _ _ hc') d (CoinWordLoader.word_length _ _ hd)⟩

#print axioms execution_source
#print axioms run_support

#print axioms next_counts
#print axioms output_charged

#print axioms commit_program_boundary
#print axioms output_work
#print axioms output_scalars
#print axioms output_proof
#print axioms output_saved
end ExplainableCrypto.Helios.Computational.PrimeProofRequest
