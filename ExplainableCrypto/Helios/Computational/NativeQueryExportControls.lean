import ExplainableCrypto.Helios.Computational.NativeQueryExportGate
import ExplainableCrypto.Helios.Computational.NativeQueryExportAdapter

/-! Independent kernel controls for the checked export-core gate. `same` checks
all six stacks, final control and memory, exact charge, and the entire query log.
The expected storage and output below are literals, not the implementation's
prefix or serializer. Actual-head adapter controls are appended separately. -/
namespace ExplainableCrypto.Helios.Computational.NativeQueryExportControls
open NativeQueryExportGate
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

theorem blank_head_storage : same
    (observe NativeQueryExport.program none [none,some true] [some true,some false]
      [true,false] [false,true,true])
    (endpoint [false,false,true,true,true,false] [] [] [false,false,true,true]
      [true,false] [false,true,true] 12) = true := by decide +kernel

theorem false_head_is_bit : same
    (observe NativeQueryExport.program (some false) [none,some true] []
      [true,false] [false,true,true])
    (endpoint [true,false] [false] [] [false,false,true,true]
      [true,false] [false,true,true] 24) = true := by decide +kernel

theorem interior_blank_retains_suffix : same
    (observe NativeQueryExport.program (some false) [none,some true]
      [some true,none,some true] [true,false] [false,true,true])
    (endpoint [true,false,true,true,false,false,true,true] [false,true] []
      [false,false,true,true] [true,false] [false,true,true] 36) = true := by decide +kernel

/-- Minimal blank-skip mutant changes retained storage and emits a false bit. -/
theorem skip_blank_regression : same
    (observe skipBlank none [none,some true] [] [true,false] [false,true,true])
    (endpoint [true,false] [false] [] [false,false,true,true]
      [true,false] [false,true,true] 24) = true := by decide +kernel

/-- False-as-blank loses the consumed encoded cell and the required output bit. -/
theorem false_as_blank_regression : same
    (observe falseAsBlank (some false) [none,some true] [] [true,false] [false,true,true])
    (endpoint [] [] [] [false,false,true,true]
      [true,false] [false,true,true] 13) = true := by decide +kernel

theorem reversal_regression : same
    (observe reverseOutput (some false) [none,some true] [some true]
      [true,false] [false,true,true])
    (endpoint [true,false,true,true] [true,false] [] [false,false,true,true]
      [true,false] [false,true,true] 36) = true := by decide +kernel

theorem retained_storage_regression : same
    (observe corruptStorage (some false) [none,some true] [] [true,false] [false,true,true])
    (endpoint [false,false] [false] [] [false,false,true,true]
      [true,false] [false,true,true] 24) = true := by decide +kernel

theorem leftover_scratch_regression : same
    (observe leaveScratch none [none,some true] [] [true,false] [false,true,true])
    (endpoint [false,false] [] [true] [false,false,true,true]
      [true,false] [false,true,true] 12) = true := by decide +kernel

namespace ActualHead
open Turing OracleComp OracleSpec
abbrev State := BitOracleMachine.Config 6 4 3

def framedCode (p : Fin 4 → NativeQueryExportAdapter.Statement) : BitOracleMachine.Code 6 4 3 :=
  BitOracleStackFrame.code (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin (3+3))
    (fun l => .compute (p l))

private def handler : QueryImpl BitOracleMachine.spec
    (StateT (List BitOracleMachine.Request) Id) :=
  fun q log => match q with
    | .coin => (false,log++[q])
    | .hash _ => ([],log++[q])

def initial (head : Cell) (before after : List Cell) (privateA privateB : List Bool) : State :=
  ⟨some 0,cellMemory head,![encode after,[],[],encode before,privateA,privateB]⟩

def observe (p : Fin 4 → NativeQueryExportAdapter.Statement) (head : Cell)
    (before after : List Cell) (privateA privateB : List Bool) :=
  (simulateQ handler (BitOracleMachine.run (framedCode p)
    (NativeQueryExportAdapter.clock head after) (initial head before after privateA privateB))).run []

def endpoint (memory : Fin 3) (source output scratch encodedBefore privateA privateB : List Bool)
    (charge : Nat) : (State × Nat) × List BitOracleMachine.Request :=
  ((⟨none,memory,![source,output,scratch,encodedBefore,privateA,privateB]⟩,charge),[])

def expected (head : Cell) (before after : List Cell) (privateA privateB : List Bool) :=
  endpoint (cellMemory head) (encode after) (scan (head::after)) []
    (encode before) privateA privateB (12*(scan (head::after)).length+18)

def same (actual target : (State × Nat) × List BitOracleMachine.Request) : Bool :=
  decide (actual.1.1.l = target.1.1.l) && decide (actual.1.1.var = target.1.1.var) &&
    (List.finRange 6).all (fun i => decide (actual.1.1.stk i = target.1.1.stk i)) &&
    decide (actual.1.2 = target.1.2) && decide (actual.2 = target.2)

/-- Compile an actual mutated core into the unchanged adapter's two live regions. -/
def withCore (p : Fin 2 → NativeQueryExport.Statement) : Fin 4 → NativeQueryExportAdapter.Statement :=
  ![NativeQueryExportAdapter.entry,
    TM2ReturnLink.redirect NativeQueryExportAdapter.coreLabel 3 (p 0),
    TM2ReturnLink.redirect NativeQueryExportAdapter.coreLabel 3 (p 1),
    NativeQueryExportAdapter.exitStmt]

def omitHead : Fin 4 → NativeQueryExportAdapter.Statement := fun l =>
  if l = 0 then .goto (fun _ => 1) else NativeQueryExportAdapter.program l

def loseHead : Fin 4 → NativeQueryExportAdapter.Statement := fun l =>
  if l = 3 then .pop 0 (fun v _ => v) (.pop 0 (fun _ _ => 0) .halt)
  else NativeQueryExportAdapter.program l

private def cellLists : Nat → List (List Cell)
  | 0 => [[]]
  | n+1 => [] :: ((cellLists n).flatMap fun xs => [none::xs,some false::xs,some true::xs])

private def cases : List (Cell × List Cell × List Cell × List Bool × List Bool) := do
  let head ← [none,some false,some true]
  let before ← cellLists 2
  let after ← cellLists 2
  let (a,b) ← [([],[]),([true,false,true],[false,true]),([false,false,true],[true,false,false,true])]
  pure (head,before,after,a,b)

def check : IO Unit := do
  let before : List Cell := [none,some true]
  let after : List Cell := [some true,some true,none,some false]
  let a := [true,false,true]
  let b := [false,true]
  let original := endpoint 1 [true,true,true,true,false,false,true,false]
    [false,true,true] [] [false,false,true,true] a b 54
  unless same (observe NativeQueryExportAdapter.program (some false) before after a b) original do
    throw (IO.userError "FAIL ADAPTER: directed full literal head/source/output/frame/scratch/charge")
  let mutants : List (String × (Fin 4 → NativeQueryExportAdapter.Statement) ×
      ((State × Nat) × List BitOracleMachine.Request)) :=
    [("skip blank",withCore skipBlank,endpoint 1
        [true,true,true,true,true,false,true,false] [false,true,true,false,false] []
        [false,false,true,true] a b 78),
      ("false as blank",withCore falseAsBlank,endpoint 2
        [true,true,false,false,true,false] [] [] [false,false,true,true] a b 19),
      ("reverse output",withCore reverseOutput,endpoint 1
        [true,true,true,true,false,false,true,false] [true,true,false] []
        [false,false,true,true] a b 54),
      ("corrupt retained storage",withCore corruptStorage,endpoint 0
        [false,true,false,true,false,false,true,false] [false,true,true] []
        [false,false,true,true] a b 54),
      ("leave scratch",withCore leaveScratch,endpoint 1
        [true,true,true,true,false,false,true,false] [false,true,true] [true]
        [false,false,true,true] a b 54),
      ("omit actual head",omitHead,endpoint 2
        [true,true,false,false,true,false] [true,true] [] [false,false,true,true] a b 40),
      ("lose restored head",loseHead,endpoint 0
        [true,true,true,true,false,false,true,false] [false,true,true] []
        [false,false,true,true] a b 54)]
  for (name,mutant,target) in mutants do
    let actual := observe mutant (some false) before after a b
    unless same actual target do
      throw (IO.userError s!"FAIL ADAPTER: independent mutant endpoint {name}")
    if same actual original then
      throw (IO.userError s!"FAIL ADAPTER: undetected mutation {name}")
  unless cases.length = 1521 do
    throw (IO.userError s!"FAIL ADAPTER: enumeration count {cases.length}")
  for (head,before,after,a,b) in cases do
    let actual := observe NativeQueryExportAdapter.program head before after a b
    unless same actual (expected head before after a b) do
      throw (IO.userError s!"FAIL ADAPTER: head={head},before={before},after={after},frame=({a},{b})")
    unless actual.1.2 ≤ NativeQueryExportAdapter.cost head after do
      throw (IO.userError "FAIL ADAPTER: original cost bound")
  IO.println "PASS ACTUAL HEAD: 1521 exhaustive +1 directed originals; seven actual code mutants; complete six stacks +restored original head +exact12k+18 charge +zeroqueries, zero discards."

/-- The existing head register and after storage are both restored literally. -/
theorem blank_head_storage : same
    (observe NativeQueryExportAdapter.program none [none,some true] [some true,some false]
      [true,false] [false,true,true])
    (endpoint 0 [true,true,true,false] [] [] [false,false,true,true]
      [true,false] [false,true,true] 18) = true := by decide +kernel

theorem false_head_is_bit : same
    (observe NativeQueryExportAdapter.program (some false) [none,some true] []
      [true,false] [false,true,true])
    (endpoint 1 [] [false] [] [false,false,true,true]
      [true,false] [false,true,true] 30) = true := by decide +kernel

theorem interior_blank_retains_suffix : same
    (observe NativeQueryExportAdapter.program (some true) [none,some true]
      [some false,none,some true] [true,false] [false,true,true])
    (endpoint 2 [true,false,false,false,true,true] [true,false] []
      [false,false,true,true] [true,false] [false,true,true] 42) = true := by decide +kernel

/-- Omitting executable head preparation emits the next cell and loses its storage. -/
theorem omitted_head_regression : same
    (observe omitHead (some false) [none,some true] [some true]
      [true,false] [false,true,true])
    (endpoint 2 [] [true] [] [false,false,true,true]
      [true,false] [false,true,true] 28) = true := by decide +kernel

theorem lost_head_regression : same
    (observe loseHead (some false) [none,some true] [] [true,false] [false,true,true])
    (endpoint 0 [] [false] [] [false,false,true,true]
      [true,false] [false,true,true] 30) = true := by decide +kernel


end ActualHead

end ExplainableCrypto.Helios.Computational.NativeQueryExportControls
