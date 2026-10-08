import ExplainableCrypto.Helios.Computational.CacheReadMachine
import ExplainableCrypto.Helios.Computational.CacheInsertMachine
import ExplainableCrypto.Helios.Computational.LogAppendMachine
import ExplainableCrypto.Helios.Computational.TM2FiniteCoordinates
import ExplainableCrypto.Helios.Computational.BinaryModuloCode
import Mathlib.Data.List.NodupEquivFin

/-! Executable coordinate tables for the existing cache routines. These use
Mathlib's list equivalence and the existing project frame/coordinate translators.
They do not implement a second parser, writer or cache algorithm. -/
namespace ExplainableCrypto.Helios.Computational.CacheRoutineCode
open Turing.TM2 BitOracleMachine OracleComp

private def natLabels : List NatPrefixMachine.Label := [.width,.payload,.restore]
/-- Existing exhaustive field-parser labels, also used by the enclosing request loader. -/
def fieldLabels : List FieldPrefixMachine.Label :=
  natLabels.map .header ++ [.field .scan,.field (.counter false),.field (.counter true),.field .restore,.enter,.finish]
private def keyLabels : List CacheKeyFieldMachine.Label :=
  [.h0,.h1,.h2,.h3,.h4,.check,.finish] ++ fieldLabels.map .field ++
    [.compare .scan,.compare (.restore false),.compare (.restore true),.compare (.clear false),.compare (.clear true)]
private def entryLabels : List CacheEntryMachine.Label :=
  keyLabels.map .key ++ fieldLabels.map (.answer false) ++ fieldLabels.map (.answer true) ++
    [.keyDone,.answerDone false,.answerDone true]
private def lookupLabels : List CacheLookupMachine.Label :=
  [.copy false,.copy true] ++ natLabels.map .count ++ fieldLabels.map .field ++ entryLabels.map .entry ++
    [.decrement false,.decrement true,.copyDone,.countDone,.loop,.fieldDone,.entryDone,.clear,.decDone]
private def writerTable : List FrameWriteMachine.Label :=
  [.increment false,.increment true,.resume,.collect,.restore,.digits,.putbits,.width]
private def readTable : List CacheReadMachine.Label :=
  lookupLabels.map .lookup ++ natLabels.map .parse ++ [.looked,.parsed]
private def insertTable : List CacheInsertMachine.Label :=
  lookupLabels.map .lookup ++ natLabels.map .parse ++ [.increment false,.increment true] ++
    [.copy false false,.copy false true,.copy true false,.copy true true] ++
    writerTable.map (.write .scalar) ++ writerTable.map (.write .key) ++
    writerTable.map (.write .entry) ++ writerTable.map (.write .final) ++
    [.lookupDone,.parseDone,.incDone,.copyDone false,.copyDone true,
      .writeDone .scalar,.writeDone .key,.writeDone .entry,.writeDone .final,.pair]
private def appendTable : List LogAppendMachine.Label :=
  natLabels.map .parse ++ [.increment false,.increment true,.copy false,.copy true] ++
    writerTable.map .write ++ writerTable.map .finish ++
    [.parseDone,.incDone,.copyDone,.writeDone,.reverse,.restore,.done]

def readSize := readTable.length
def insertSize := insertTable.length
def writerSize := writerTable.length
def appendSize := appendTable.length
instance : NeZero readSize := ⟨by decide +kernel⟩
instance : NeZero insertSize := ⟨by decide +kernel⟩
instance : NeZero writerSize := ⟨by decide +kernel⟩
instance : NeZero appendSize := ⟨by decide +kernel⟩

def readLabels : CacheReadMachine.Label ≃ Fin readSize :=
  (List.Nodup.getEquivOfForallMemList readTable (by decide +kernel) (by decide +kernel)).symm

def insertLabels : CacheInsertMachine.Label ≃ Fin insertSize :=
  (List.Nodup.getEquivOfForallMemList insertTable (by decide +kernel) (by decide +kernel)).symm

def writerLabels : FrameWriteMachine.Label ≃ Fin writerSize :=
  (List.Nodup.getEquivOfForallMemList writerTable (by decide +kernel) (by decide +kernel)).symm

def appendLabels : LogAppendMachine.Label ≃ Fin appendSize :=
  (List.Nodup.getEquivOfForallMemList appendTable (by decide +kernel) (by decide +kernel)).symm

private def readPorts : CacheReadMachine.Stack ≃ Fin 8 :=
  (List.Nodup.getEquivOfForallMemList
    [CacheLookupMachine.src,CacheLookupMachine.cnt,CacheLookupMachine.temp,CacheLookupMachine.out,
      CacheLookupMachine.outer,CacheLookupMachine.archive,CacheLookupMachine.query,CacheLookupMachine.saved]
    (by decide +kernel) (by
      intro x
      rcases x with (((k|b)|u)|v)
      · cases k <;> simp [CacheLookupMachine.src,CacheLookupMachine.cnt,CacheLookupMachine.temp,CacheLookupMachine.out]
      · cases b <;> simp [CacheLookupMachine.outer,CacheLookupMachine.archive]
      · cases u; simp [CacheLookupMachine.query]
      · cases v; simp [CacheLookupMachine.saved])).symm

private def insertPorts : CacheInsertMachine.Stack ≃ Fin 9 :=
  (List.Nodup.getEquivOfForallMemList
    [CacheInsertMachine.src,CacheInsertMachine.cnt,CacheInsertMachine.temp,CacheInsertMachine.out,
      CacheInsertMachine.outer,CacheInsertMachine.archive,CacheInsertMachine.query,CacheInsertMachine.saved,
      CacheInsertMachine.answer] (by decide +kernel) (by
        intro x
        rcases x with ((((k|b)|u)|v)|w)
        · cases k <;> simp [CacheInsertMachine.src,CacheInsertMachine.cnt,CacheInsertMachine.temp,CacheInsertMachine.out]
        · cases b <;> simp [CacheInsertMachine.outer,CacheInsertMachine.archive]
        · cases u; simp [CacheInsertMachine.query]
        · cases v; simp [CacheInsertMachine.saved]
        · cases w; simp [CacheInsertMachine.answer])).symm

private def writerPorts : FrameWriteMachine.Stack ≃ Fin 5 :=
  (List.Nodup.getEquivOfForallMemList
    [FrameWriteMachine.input,FrameWriteMachine.carry,FrameWriteMachine.buffer,
      FrameWriteMachine.output,FrameWriteMachine.counter] (by decide +kernel) (by
        intro x
        rcases x with (k|u)
        · cases k <;> simp [FrameWriteMachine.input,FrameWriteMachine.carry,FrameWriteMachine.buffer,FrameWriteMachine.output]
        · cases u; simp [FrameWriteMachine.counter])).symm

private def appendPorts : LogAppendMachine.Stack ≃ Fin 8 :=
  (List.Nodup.getEquivOfForallMemList
    [.src,.carry,.scratch,.out,.count,.temp,.key,.body] (by decide +kernel)
    (by intro x; cases x <;> decide)).symm

/-- Probe work uses 0–5, key 8 and original-cache archive 9. Extra ports are 6,7,10,11. -/
def readLayout : CacheReadMachine.Stack ⊕ Fin 4 ≃ Fin 12 :=
  ((Equiv.sumCongr readPorts (Equiv.refl _)).trans finSumFinEquiv).trans
    (List.Nodup.getEquivOfForallMemList [0,1,2,3,4,5,8,9,6,7,10,11]
      (by decide +kernel) (by decide +kernel))

/-- Insertion retains key/cache/answer on 8/9/7. Extra ports are 6,10,11. -/
def insertLayout : CacheInsertMachine.Stack ⊕ Fin 3 ≃ Fin 12 :=
  ((Equiv.sumCongr insertPorts (Equiv.refl _)).trans finSumFinEquiv).trans
    (List.Nodup.getEquivOfForallMemList [0,1,2,3,4,5,8,9,7,6,10,11]
      (by decide +kernel) (by decide +kernel))

/-- Hit writer consumes digits 3, returns encoding 7; extras are 4,5,6,8,9,10,11. -/
def writerLayout : FrameWriteMachine.Stack ⊕ Fin 7 ≃ Fin 12 :=
  ((Equiv.sumCongr writerPorts (Equiv.refl _)).trans finSumFinEquiv).trans
    (List.Nodup.getEquivOfForallMemList [0,1,2,7,3,4,5,6,8,9,10,11]
      (by decide +kernel) (by decide +kernel))

/-- Log append consumes log 10, returns log 6, keeps key 8; extras are 3,7,9,11. -/
def appendLayout : LogAppendMachine.Stack ⊕ Fin 4 ≃ Fin 12 :=
  ((Equiv.sumCongr appendPorts (Equiv.refl _)).trans finSumFinEquiv).trans
    (List.Nodup.getEquivOfForallMemList [0,1,2,6,4,5,8,10,3,7,9,11]
      (by decide +kernel) (by decide +kernel))

def readCode := TM2FiniteCoordinates.program (Equiv.refl (Fin 12)) readLabels BinaryModuloCode.memory
  (fun l => TM2StackFrame.relocate readLayout (CacheReadMachine.program l))
def insertCode := TM2FiniteCoordinates.program (Equiv.refl (Fin 12)) insertLabels BinaryModuloCode.memory
  (fun l => TM2StackFrame.relocate insertLayout (CacheInsertMachine.program l))
def writerCode := TM2FiniteCoordinates.program (Equiv.refl (Fin 12)) writerLabels BinaryModuloCode.memory
  (fun l => TM2StackFrame.relocate writerLayout (FrameWriteMachine.program l))
def appendCode := TM2FiniteCoordinates.program (Equiv.refl (Fin 12)) appendLabels BinaryModuloCode.memory
  (fun l => TM2StackFrame.relocate appendLayout (LogAppendMachine.program l))

def readState (cfg : CacheReadMachine.Config) (frame : Fin 4 → List Bool) :=
  TM2FiniteCoordinates.present (Equiv.refl _) readLabels BinaryModuloCode.memory (TM2StackFrame.embed readLayout cfg frame)
def insertState (cfg : CacheInsertMachine.Config) (frame : Fin 3 → List Bool) :=
  TM2FiniteCoordinates.present (Equiv.refl _) insertLabels BinaryModuloCode.memory (TM2StackFrame.embed insertLayout cfg frame)
def writerState (cfg : FrameWriteMachine.Config) (frame : Fin 7 → List Bool) :=
  TM2FiniteCoordinates.present (Equiv.refl _) writerLabels BinaryModuloCode.memory (TM2StackFrame.embed writerLayout cfg frame)
def appendState (cfg : LogAppendMachine.Config) (frame : Fin 4 → List Bool) :=
  TM2FiniteCoordinates.present (Equiv.refl _) appendLabels BinaryModuloCode.memory (TM2StackFrame.embed appendLayout cfg frame)

set_option maxRecDepth 8192 in
private theorem read_cost : ∀ label, localCost (readCode label) ≤ 32 := by decide +kernel
set_option maxRecDepth 8192 in
private theorem insert_cost : ∀ label, localCost (insertCode label) ≤ 32 := by decide +kernel
private theorem writer_cost : ∀ label, localCost (writerCode label) ≤ 32 := by decide +kernel
private theorem append_cost : ∀ label, localCost (appendCode label) ≤ 32 := by decide +kernel

/-- Exact translated probe run, including arbitrary intermediate states and frame. -/
theorem read_run (fuel : Nat) (cfg : CacheReadMachine.Config) (frame : Fin 4 → List Bool) :
    ∃ charge ≤ 32*fuel,
      run (fun l => .compute (readCode l)) fuel (readState cfg frame) =
        pure (readState (CacheReadMachine.tick^[fuel] cfg) frame,charge) := by
  obtain ⟨charge,hc,hr⟩ := compute_run_cost readCode 32 read_cost fuel (readState cfg frame)
  refine ⟨charge,hc,?_⟩
  rw [hr]
  congr 2
  rw [readState,readCode,TM2FiniteCoordinates.run,TM2StackFrame.run]
  rfl

theorem insert_run (fuel : Nat) (cfg : CacheInsertMachine.Config) (frame : Fin 3 → List Bool) :
    ∃ charge ≤ 32*fuel,
      run (fun l => .compute (insertCode l)) fuel (insertState cfg frame) =
        pure (insertState (CacheInsertMachine.tick^[fuel] cfg) frame,charge) := by
  obtain ⟨charge,hc,hr⟩ := compute_run_cost insertCode 32 insert_cost fuel (insertState cfg frame)
  refine ⟨charge,hc,?_⟩
  rw [hr]
  congr 2
  rw [insertState,insertCode,TM2FiniteCoordinates.run,TM2StackFrame.run]
  rfl

theorem writer_run (fuel : Nat) (cfg : FrameWriteMachine.Config) (frame : Fin 7 → List Bool) :
    ∃ charge ≤ 32*fuel,
      run (fun l => .compute (writerCode l)) fuel (writerState cfg frame) =
        pure (writerState (FrameWriteMachine.tick^[fuel] cfg) frame,charge) := by
  obtain ⟨charge,hc,hr⟩ := compute_run_cost writerCode 32 writer_cost fuel (writerState cfg frame)
  refine ⟨charge,hc,?_⟩
  rw [hr]
  congr 2
  rw [writerState,writerCode,TM2FiniteCoordinates.run,TM2StackFrame.run]
  rfl

theorem append_run (fuel : Nat) (cfg : LogAppendMachine.Config) (frame : Fin 4 → List Bool) :
    ∃ charge ≤ 32*fuel,
      run (fun l => .compute (appendCode l)) fuel (appendState cfg frame) =
        pure (appendState (LogAppendMachine.tick^[fuel] cfg) frame,charge) := by
  obtain ⟨charge,hc,hr⟩ := compute_run_cost appendCode 32 append_cost fuel (appendState cfg frame)
  refine ⟨charge,hc,?_⟩
  rw [hr]
  congr 2
  rw [appendState,appendCode,TM2FiniteCoordinates.run,TM2StackFrame.run]
  rfl

/-- Probe entry uses the supplied original cache on work port 0. Its own copy
establishes the retained cache on 9; all other work starts empty. -/
def probeStart (key cache log record : List Bool) : Config 12 readSize 3 :=
  ⟨some 0,0,![cache,[],[],[],[],[],[],[],key,[],log,record]⟩

def probeMiss (key cache log record : List Bool) : Config 12 readSize 3 :=
  ⟨none,1,![[],[],[],[],[],[],[],[],key,cache,log,record]⟩

def probeHit (key cache log record digits counter tail : List Bool) : Config 12 readSize 3 :=
  ⟨none,2,![tail,[],[],digits,counter,[],[],[],key,cache,log,record]⟩

private theorem probe_start (key cache log record : List Bool) :
    readState (CacheReadMachine.start key cache) ![[],[],log,record] = probeStart key cache log record := by
  change (⟨_,_,_⟩ : Config 12 readSize 3) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

/-- Actual source-generated misses establish the empty sampler workspace on the
common caller layout, preserving the arbitrary log and operand record. -/
theorem probe_miss {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q)) (key : BallotForkPoint (PrimeGroup p q))
    (log record : List Bool) (h : cache.lookup key = none) :
    ∃ fuel ≤ CacheReadMachine.cost p q cache.entries.length ((ballotCacheBitCodec p q).encode cache).length,
      ∃ charge ≤ 32*fuel,
      run (fun l => .compute (readCode l)) fuel
        (probeStart ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache) log record) =
      pure (probeMiss ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache) log record,charge) := by
  obtain ⟨fuel,hf,hr⟩ := CacheReadMachine.miss_run cache key h
  obtain ⟨charge,hc,he⟩ := read_run fuel
    (CacheReadMachine.start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)) ![[],[],log,record]
  rw [probe_start,hr] at he
  refine ⟨fuel,hf,charge,hc,he.trans ?_⟩
  congr 2
  change (⟨_,_,_⟩ : Config 12 readSize 3) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

/-- Actual hit digits and residual scratch are retained on their caller ports;
the next phase must execute its cleanup instead of supplying clean scratch. -/
theorem probe_hit {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q)) (key : BallotForkPoint (PrimeGroup p q))
    (a : ZMod q) (log record : List Bool) (h : cache.lookup key = some a) :
    ∃ fuel ≤ CacheReadMachine.cost p q cache.entries.length ((ballotCacheBitCodec p q).encode cache).length,
      ∃ charge ≤ 32*fuel, ∃ n tail,
      run (fun l => .compute (readCode l)) fuel
        (probeStart ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache) log record) =
      pure (probeHit ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)
        log record a.val.bits (n+1).bits tail,charge) := by
  obtain ⟨fuel,hf,n,tail,hr⟩ := CacheReadMachine.hit_run cache key a h
  obtain ⟨charge,hc,he⟩ := read_run fuel
    (CacheReadMachine.start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)) ![[],[],log,record]
  rw [probe_start,hr] at he
  refine ⟨fuel,hf,charge,hc,n,tail,he.trans ?_⟩
  congr 2
  change (⟨_,_,_⟩ : Config 12 readSize 3) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

end ExplainableCrypto.Helios.Computational.CacheRoutineCode
