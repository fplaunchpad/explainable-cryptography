import ExplainableCrypto.Helios.Computational.NativeQueryExport
import ExplainableCrypto.Helios.Computational.BitOracleStackFrame

/-! Export-core enquiry: does the actual executable two-label core retain all
encoded cells and arbitrary framed words, export exactly the contiguous prefix,
clean its scratch, and charge 12k+12? Small falsifiers are a blank head followed
by a bit, false at the head, or data after an interior blank. Independent oracle:
explicit two-bit encoding and recursive first-blank scan below, never execution
of the implementation. The finite gate enumerates 1,521 head/before/after/frame
combinations and directed literals. This core receives cells(head::after);
constructing that word from a native head register remains an executed adapter
obligation. NativeQueryExportControls adds the actual adapter when available. -/
namespace ExplainableCrypto.Helios.Computational.NativeQueryExportGate
open Turing.TM2 OracleComp OracleSpec
abbrev Cell := Option Bool
abbrev State := BitOracleMachine.Config 6 2 3

def encode : List Cell → List Bool
  | [] => []
  | none::rest => false::false::encode rest
  | some false::rest => true::false::encode rest
  | some true::rest => true::true::encode rest

def scan : List Cell → List Bool
  | [] | none::_ => []
  | some b::rest => b::scan rest

def cellMemory : Cell → Fin 3
  | none => 0
  | some false => 1
  | some true => 2

private def handler : QueryImpl BitOracleMachine.spec
    (StateT (List BitOracleMachine.Request) Id) :=
  fun q log => match q with
    | .coin => (false,log++[q])
    | .hash _ => ([],log++[q])

def framedCode (p : Fin 2 → NativeQueryExport.Statement) : BitOracleMachine.Code 6 2 3 :=
  BitOracleStackFrame.code (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin (3+3)) (fun l => .compute (p l))

def initial (head : Cell) (before after : List Cell) (privateA privateB : List Bool) : State :=
  ⟨some 0,cellMemory head,![encode (head::after),[],[],encode before,privateA,privateB]⟩

def observe (p : Fin 2 → NativeQueryExport.Statement) (head : Cell)
    (before after : List Cell) (privateA privateB : List Bool) :=
  (simulateQ handler (BitOracleMachine.run (framedCode p)
    (NativeQueryExport.clock (head::after)) (initial head before after privateA privateB))).run []

def endpoint (source output scratch encodedBefore privateA privateB : List Bool) (charge : Nat) :
    (State × Nat) × List BitOracleMachine.Request :=
  ((⟨none,0,![source,output,scratch,encodedBefore,privateA,privateB]⟩,charge),[])

def expected (head : Cell) (before after : List Cell) (privateA privateB : List Bool) :=
  endpoint (encode (head::after)) (scan (head::after)) [] (encode before) privateA privateB
    (12*(scan (head::after)).length+12)

def same (actual target : (State × Nat) × List BitOracleMachine.Request) : Bool :=
  decide (actual.1.1.l = target.1.1.l) && decide (actual.1.1.var = target.1.1.var) &&
    (List.finRange 6).all (fun i => decide (actual.1.1.stk i = target.1.1.stk i)) &&
    decide (actual.1.2 = target.1.2) && decide (actual.2 = target.2)

/-- Actual scan predicate mutation: a stored blank tag is treated as a bit. -/
def skipBlank : Fin 2 → NativeQueryExport.Statement := fun l => if l = 0 then
  .peek 0 (fun _ b => BitTapeCoverage.cellCode b)
    (.branch (fun v => v ≠ 0)
      (.pop 0 (fun v _ => v) (.pop 0 (fun _ b => BitTapeCoverage.cellCode b)
        (.push 2 (fun v => v = 2) (.goto (fun _ => 0)))))
      (.goto (fun _ => 1)))
  else NativeQueryExport.program l

/-- Actual decoder mutation: a false payload stops the scan after consuming it. -/
def falseAsBlank : Fin 2 → NativeQueryExport.Statement := fun l => if l = 0 then
  .peek 0 (fun _ b => BitTapeCoverage.cellCode b)
    (.branch (fun v => v = 2)
      (.pop 0 (fun v _ => v) (.pop 0 (fun _ b => BitTapeCoverage.cellCode b)
        (.branch (fun v => v = 2)
          (.push 2 (fun _ => true) (.goto (fun _ => 0))) (.goto (fun _ => 1)))))
      (.goto (fun _ => 1)))
  else NativeQueryExport.program l

/-- Actual data-flow mutation: accumulate output during the forward scan. -/
def reverseOutput : Fin 2 → NativeQueryExport.Statement := fun l => if l = 0 then
  .peek 0 (fun _ b => BitTapeCoverage.cellCode b)
    (.branch (fun v => v = 2)
      (.pop 0 (fun v _ => v) (.pop 0 (fun _ b => BitTapeCoverage.cellCode b)
        (.push 2 (fun v => v = 2) (.push 1 (fun v => v = 2) (.goto (fun _ => 0))))))
      (.goto (fun _ => 1)))
  else
    .pop 2 (fun _ b => BitTapeCoverage.cellCode b)
      (.branch (fun v => v ≠ 0)
        (.push 0 (fun v => v = 2) (.push 0 (fun _ => true) (.goto (fun _ => 1))))
        (.load (fun _ => 0) .halt))

/-- Actual restoration mutation corrupts each retained nonblank tag. -/
def corruptStorage : Fin 2 → NativeQueryExport.Statement := fun l => if l = 1 then
  .pop 2 (fun _ b => BitTapeCoverage.cellCode b)
    (.branch (fun v => v ≠ 0)
      (.push 0 (fun v => v = 2) (.push 0 (fun _ => false)
        (.push 1 (fun v => v = 2) (.goto (fun _ => 1)))))
      (.load (fun _ => 0) .halt))
  else NativeQueryExport.program l

/-- Actual terminal mutation leaves one bit of scratch. -/
def leaveScratch : Fin 2 → NativeQueryExport.Statement := fun l => if l = 1 then
  .pop 2 (fun _ b => BitTapeCoverage.cellCode b)
    (.branch (fun v => v ≠ 0)
      (.push 0 (fun v => v = 2) (.push 0 (fun _ => true)
        (.push 1 (fun v => v = 2) (.goto (fun _ => 1)))))
      (.load (fun _ => 0) (.push 2 (fun _ => true) .halt)))
  else NativeQueryExport.program l

private def cellLists : Nat → List (List Cell)
  | 0 => [[]]
  | n+1 => [] :: ((cellLists n).flatMap fun xs => [none::xs,some false::xs,some true::xs])

private def frames : List (List Bool × List Bool) :=
  [([],[]),([true,false,true],[false,true]),([false,false,true],[true,false,false,true])]

private def cases : List (Cell × List Cell × List Cell × List Bool × List Bool) := do
  let head ← [none,some false,some true]
  let before ← cellLists 2
  let after ← cellLists 2
  let (a,b) ← frames
  pure (head,before,after,a,b)

def check : IO Unit := do
  let before : List Cell := [none,some true]
  let after : List Cell := [some true,some true,none,some false]
  let a := [true,false,true]
  let b := [false,true]
  let literalOriginal := endpoint
    [true,false,true,true,true,true,false,false,true,false] [false,true,true] []
    [false,false,true,true] a b 48
  unless same (observe NativeQueryExport.program (some false) before after a b) literalOriginal do
    throw (IO.userError "FAIL: directed full literal source/output/frame/scratch/charge")
  let mutants : List (String × (Fin 2 → NativeQueryExport.Statement) ×
      ((State × Nat) × List BitOracleMachine.Request)) :=
    [("skip blank",skipBlank,endpoint
        [true,false,true,true,true,true,true,false,true,false] [false,true,true,false,false] []
        [false,false,true,true] a b 72),
      ("false as blank",falseAsBlank,endpoint
        [true,true,true,true,false,false,true,false] [] [] [false,false,true,true] a b 13),
      ("reverse output",reverseOutput,endpoint
        [true,false,true,true,true,true,false,false,true,false] [true,true,false] []
        [false,false,true,true] a b 48),
      ("corrupt retained storage",corruptStorage,endpoint
        [false,false,false,true,false,true,false,false,true,false] [false,true,true] []
        [false,false,true,true] a b 48),
      ("leave scratch",leaveScratch,endpoint
        [true,false,true,true,true,true,false,false,true,false] [false,true,true] [true]
        [false,false,true,true] a b 48)]
  for (name,mutant,target) in mutants do
    let actual := observe mutant (some false) before after a b
    unless same actual target do
      throw (IO.userError s!"FAIL: independently expected mutant endpoint {name}")
    if same actual literalOriginal then
      throw (IO.userError s!"FAIL: undetected actual instruction mutation {name}")
  unless cases.length = 1521 do
    throw (IO.userError s!"FAIL: enumeration count {cases.length}")
  for (head,before,after,a,b) in cases do
    let actual := observe NativeQueryExport.program head before after a b
    unless same actual (expected head before after a b) do
      throw (IO.userError s!"FAIL: head={head},before={before},after={after},frame=({a},{b})")
    unless actual.1.2 ≤ NativeQueryExport.cost (head::after) do
      throw (IO.userError "FAIL: original declared cost exceeded")
  IO.println "PASS CORE: 1521 exhaustive +1 directed original; five actual instruction mutants with independent full endpoints/charges; six ports/memory/halt/zeroqueries; zero discards. Actual head-register adapter not claimed by this core gate."

end ExplainableCrypto.Helios.Computational.NativeQueryExportGate
