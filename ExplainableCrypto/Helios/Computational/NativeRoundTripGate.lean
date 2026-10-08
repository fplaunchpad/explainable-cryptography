import ExplainableCrypto.Helios.Computational.NativeAnswerImport
import ExplainableCrypto.Helios.Computational.NativeRoundTrip

/-! Round-trip feasibility gates. The importer candidate consumes old answer
before-storage and raw-query scratch, encodes a raw reply in native order, and
retains every framed private word. Independent oracle: literal tagged encoding
and elementary length arithmetic below, not an implementation evaluator.
Small falsifiers: empty reply with nonempty old storage; false first reply bit;
uncleared query; reversed reply; wrong continuation in the enclosing round trip.
All finite cases are constructed, with no implication discards. -/
namespace ExplainableCrypto.Helios.Computational.NativeRoundTripGate
open Turing OracleComp OracleSpec
abbrev Cell := Option Bool

def encodeCells : List Cell → List Bool
  | [] => []
  | none::rest => false::false::encodeCells rest
  | some false::rest => true::false::encodeCells rest
  | some true::rest => true::true::encodeCells rest

def cellMemory : Cell → Fin 3
  | none => 0
  | some false => 1
  | some true => 2

def scanWord : List Cell → List Bool
  | [] | none::_ => []
  | some b::rest => b::scanWord rest

def bitWords : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => [] :: ((bitWords n).flatMap fun w => [false::w,true::w])

def replyHandler (reply : List Bool) (coin : Bool) : QueryImpl BitOracleMachine.spec
    (StateT (List BitOracleMachine.Request) Id) :=
  fun q log => match q with
    | .coin => (coin,log++[q])
    | .hash _ => (reply,log++[q])

def same {s l m : Nat}
    (actual target : (BitOracleMachine.Config s l m × Nat) × List BitOracleMachine.Request) : Bool :=
  decide (actual.1.1.l = target.1.1.l) && decide (actual.1.1.var = target.1.1.var) &&
    (List.finRange s).all (fun i => decide (actual.1.1.stk i = target.1.1.stk i)) &&
    decide (actual.1.2 = target.1.2) && decide (actual.2 = target.2)

namespace Importer
abbrev State := BitOracleMachine.Config 6 5 3

def framedCode (p : Fin 5 → NativeAnswerImport.Statement) : BitOracleMachine.Code 6 5 3 :=
  BitOracleStackFrame.code (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin (3+3))
    (fun l => .compute (p l))

def initial (oldBefore reply query : List Bool) (frame : Fin 3 → List Bool) : State :=
  ⟨some 0,0,![oldBefore,reply,query,frame 0,frame 1,frame 2]⟩

def observe (p : Fin 5 → NativeAnswerImport.Statement) (oldBefore reply query : List Bool)
    (frame : Fin 3 → List Bool) :=
  (simulateQ (replyHandler [] false) (BitOracleMachine.run (framedCode p)
    (NativeAnswerImport.clock oldBefore reply query) (initial oldBefore reply query frame))).run []

def endpoint (memory : Fin 3) (before after query : List Bool) (frame : Fin 3 → List Bool)
    (charge : Nat) : (State × Nat) × List BitOracleMachine.Request :=
  ((⟨none,memory,![before,after,query,frame 0,frame 1,frame 2]⟩,charge),[])

def expected (oldBefore reply query : List Bool) (frame : Fin 3 → List Bool) :=
  endpoint (cellMemory reply.head?) [] (encodeCells (reply.tail.map some)) [] frame
    (3*oldBefore.length+3*query.length+9*reply.length+18)

/-- Actual instruction changes which stack the first cleanup consumes. -/
def wrongClear : Fin 5 → NativeAnswerImport.Statement := fun l =>
  if l = 0 then NativeAnswerImport.clear 1 0 1 else NativeAnswerImport.program l

def leaveQuery : Fin 5 → NativeAnswerImport.Statement := fun l =>
  if l = 1 then .goto (fun _ => 2) else NativeAnswerImport.program l

def skipHead : Fin 5 → NativeAnswerImport.Statement := fun l =>
  if l = 4 then .halt else NativeAnswerImport.program l

private def frames : List (Fin 3 → List Bool) :=
  [![[],[],[]],![[false,false,true,true],[true,false,true],[false,true]],
    ![[true,false,false,false],[false,true,true],[true,true,false]]]

private def cases : List (List Bool × List Bool × List Bool × (Fin 3 → List Bool)) := do
  let oldBefore ← bitWords 2
  let reply ← bitWords 3
  let query ← bitWords 2
  let frame ← frames
  pure (oldBefore,reply,query,frame)

def check : IO Unit := do
  let frame : Fin 3 → List Bool := ![[false,false,true,true],[true,false,true],[false,true]]
  let original := endpoint 1 [] [true,true,true,true] [] frame 57
  unless same (observe NativeAnswerImport.program [true,false] [false,true,true] [false,true] frame)
      original do
    throw (IO.userError "FAIL IMPORT: full literal false-first/replacement/order/frame/cost")
  let mutants : List (String × (Fin 5 → NativeAnswerImport.Statement) ×
      ((State × Nat) × List BitOracleMachine.Request)) :=
    [("wrong clear port",wrongClear,endpoint 1 [] [true,true] [] frame 43),
     ("uncleared raw query",leaveQuery,endpoint 1 [] [true,true,true,true] [false,true] frame 49),
     ("skipped head extraction",skipHead,endpoint 0 [] [true,false,true,true,true,true] [] frame 55)]
  for (name,mutant,target) in mutants do
    let actual := observe mutant [true,false] [false,true,true] [false,true] frame
    unless same actual target do
      throw (IO.userError s!"FAIL IMPORT: independent full mutant endpoint {name}")
    if same actual original then throw (IO.userError s!"FAIL IMPORT: undetected actual mutation {name}")
  unless cases.length = 2205 do throw (IO.userError s!"FAIL IMPORT: count {cases.length}")
  for (oldBefore,reply,query,frame) in cases do
    let actual := observe NativeAnswerImport.program oldBefore reply query frame
    unless same actual (expected oldBefore reply query frame) do
      throw (IO.userError s!"FAIL IMPORT: before={oldBefore},reply={reply},query={query}")
    unless actual.1.2 ≤ NativeAnswerImport.cost oldBefore reply query do
      throw (IO.userError "FAIL IMPORT: declared cost exceeded")
  IO.println "PASS IMPORTER: 2205 exhaustive +1 directed originals;3 actual instruction mutants, fullsix state/nativehead/exact3B+3Q+9R+18 charge/zeroqueries/privateframe; zero discards."

end Importer
namespace RoundTrip
abbrev State := BitOracleMachine.Config 10 81 81
abbrev Code := BitOracleMachine.Code 8 81 81

/-- One native transition selects its event from work head and continuation from
old answer head. Resumption must not reselect using the replacement reply. -/
def native (toggle : Bool) : NativeOracleTape.Code 3 := fun q h =>
  if q = 0 then .oracle
    (if toggle != (h 0 == some false) then .coin else .hash)
    (if h 2 = some true then 2 else 1)
  else .halt

def encodedMemory (work query answer : Cell) : Fin 81 :=
  ⟨27*(cellMemory work).val+9*(cellMemory query).val+3*(cellMemory answer).val,by
    have := (cellMemory work).isLt; have := (cellMemory query).isLt
    have := (cellMemory answer).isLt; omega⟩

def initial (h : Fin 3 → Cell) (before after : Fin 3 → List Cell)
    (privateA privateB : List Bool) : State :=
  ⟨some 0,encodedMemory (h 0) (h 1) (h 2),
    ![encodeCells (before 0),encodeCells (after 0),encodeCells (before 1),encodeCells (after 1),
      encodeCells (before 2),encodeCells (after 2),[],[],privateA,privateB]⟩

def framedCode (p : Code) : BitOracleMachine.Code 10 81 81 :=
  BitOracleStackFrame.code (finSumFinEquiv : Fin 8 ⊕ Fin 2 ≃ Fin (8+2)) p

/-- Gate-only bounded observation: execute actual source steps until a live
native label is reached. No tape transition or instruction is reimplemented. -/
def toReturn (p : BitOracleMachine.Code 10 81 81) : Nat → State →
    OracleComp BitOracleMachine.spec (State × Nat)
  | 0,cfg => pure (cfg,0)
  | n+1,cfg =>
    if cfg.l.any (fun label => label.val < 3) then pure (cfg,0)
    else do
      let step ← BitOracleMachine.step p cfg
      let rest ← toReturn p n step.1
      pure (rest.1,step.2+rest.2)

def observe (p : Code) (h : Fin 3 → Cell) (before after : Fin 3 → List Cell)
    (privateA privateB reply : List Bool) (coin : Bool) :=
  let fuel := 4*((after 1).length+1)+2*(before 2).length+2*reply.length+40
  (simulateQ (replyHandler reply coin) (do
    let first ← BitOracleMachine.step (framedCode p) (initial h before after privateA privateB)
    let rest ← toReturn (framedCode p) fuel first.1
    pure (rest.1,first.2+rest.2))).run []

def endpoint (next : Fin 81) (memory : Fin 81) (words : Fin 10 → List Bool)
    (charge : Nat) (events : List BitOracleMachine.Request) :
    (State × Nat) × List BitOracleMachine.Request := ((⟨some next,memory,words⟩,charge),events)

def expected (toggle : Bool) (h : Fin 3 → Cell) (before after : Fin 3 → List Cell)
    (privateA privateB reply : List Bool) (coin : Bool) :=
  let isCoin := toggle != (h 0 == some false)
  let answer := if isCoin then [coin] else reply
  let query := scanWord (h 1::after 1)
  let eventCharge := if isCoin then 2+(encodeCells (after 2)).length
    else 1+query.length+(encodeCells (after 2)).length+answer.length
  endpoint (if h 2 = some true then 2 else 1)
    (encodedMemory (h 0) (h 1) answer.head?)
    ![encodeCells (before 0),encodeCells (after 0),encodeCells (before 1),encodeCells (after 1),
      [],encodeCells (answer.tail.map some),[],[],privateA,privateB]
    (44+15*query.length+3*(encodeCells (before 2)).length+9*answer.length+eventCharge)
    [if isCoin then .coin else .hash query]

/-- Actual final return mutation, after the answer memory is restored. -/
def wrongReturn (p : Code) : Code := fun l =>
  if l = NativeRoundTrip.blockLabel (2 : Fin 3) 0 12 then
    .compute (.load (fun v => NativeRoundTrip.memory
      ![NativeRoundTrip.currentHeads v 0,NativeRoundTrip.currentHeads v 1,
        BitTapeCoverage.readCell (NativeRoundTrip.localMemory v)]) (.goto (fun _ => 1)))
  else p l

def wrongAnswerPort (p : Code) : Code := fun l =>
  if l = NativeRoundTrip.blockLabel (2 : Fin 3) 0 5 then
    .hash 6 4 (NativeRoundTrip.blockLabel (2 : Fin 3) 0 6)
  else p l

def wrongQueryPort (p : Code) : Code := fun l =>
  if l = NativeRoundTrip.blockLabel (2 : Fin 3) 0 5 then
    .hash 1 5 (NativeRoundTrip.blockLabel (2 : Fin 3) 0 6)
  else p l

def corruptStorage (port : Fin 8) (p : Code) : Code := fun l =>
  if l = NativeRoundTrip.blockLabel (2 : Fin 3) 0 12 then match p l with
    | .compute stmt => .compute (.push port (fun _ => true) stmt)
    | other => other
  else p l

/-- Incorrectly recompute the continuation using the new answer head. -/
def lateReturn (p : Code) : Code := fun l =>
  if l = NativeRoundTrip.blockLabel (2 : Fin 3) 0 12 then
    .compute (.load (fun v => NativeRoundTrip.memory
      ![NativeRoundTrip.currentHeads v 0,NativeRoundTrip.currentHeads v 1,
        BitTapeCoverage.readCell (NativeRoundTrip.localMemory v)])
      (.goto (fun v => if NativeRoundTrip.currentHeads v 2 = some true then 2 else 1)))
  else p l

private def shortCells : List (List Cell) := [[],[none],[some false],[some true]]
private def storage (i : Fin 3) :
    List Cell × List Cell × List Cell × List Cell × List Bool × List Bool :=
  if i = 0 then ([],[],[],[],[],[])
  else if i = 1 then ([none,some true],[some false,none],[some false,none],[none,some true],
    [false,true,false],[true,false,true,true])
  else ([some true,none],[none,some false],[none,some false],[some true,none,some false],
    [true,true,false],[false,true,true,false])

private def cases : List ((Fin 3 → Cell) × (Fin 3 → List Cell) ×
    (Fin 3 → List Cell) × List Bool × List Bool × Bool × List Bool × Bool) := do
  let wh ← [none,some false,some true]
  let qh ← [none,some false,some true]
  let ah ← [none,some false,some true]
  let qb ← shortCells
  let qa ← shortCells
  let i ← List.finRange 3
  let (isCoin,reply,coin) ← [(false,[],false),(false,[false],false),(false,[true],false),
    (true,[],false),(true,[],true)]
  let (wb,wa,ab,aa,a,b) := storage i
  pure (![wh,qh,ah],![wb,qb,ab],![wa,qa,aa],a,b,isCoin != (wh == some false),reply,coin)

/-- All original storage words are literal and pairwise distinguishable. -/
def fixtureWords : Fin 10 → List Bool :=
  ![[false,false,true,true],[true,true,false,false,true,false],[true,false],
    [true,true,false,false,true,true],[],[true,true,true,true],[],[],
    [false,true,false],[true,false,true,true]]

def fixtureHeads : Fin 3 → Cell := ![some false,some false,some true]
def fixtureBefore : Fin 3 → List Cell := ![[none,some true],[some false],[some false,none]]
def fixtureAfter : Fin 3 → List Cell :=
  ![[some true,none,some false],[some true,none,some true],[none,some false,some true]]

def check : IO Unit := do
  let a := [false,true,false]
  let b := [true,false,true,true]
  let p := NativeRoundTrip.code (native true)
  let original := endpoint 2 39 fixtureWords 125 [.hash [false,true]]
  unless same (observe p fixtureHeads fixtureBefore fixtureAfter a b [false,true,true] false) original do
    throw (IO.userError "FAIL ROUNDTRIP: directed full literal hash replacement/live continuation/storage/charge")
  let badAnswer := Function.update fixtureWords (5 : Fin 10)
    [true,false,true,true,true,false,true,true,true,true]
  let badWork := Function.update fixtureWords (0 : Fin 10) [true,false,false,true,true]
  let badScratch := Function.update fixtureWords (7 : Fin 10) [true]
  let mutants : List (String × Code × ((State × Nat) × List BitOracleMachine.Request)) :=
    [("wrong live return",wrongReturn p,endpoint 1 39 fixtureWords 125 [.hash [false,true]]),
     ("late reply-based return",lateReturn p,endpoint 1 39 fixtureWords 125 [.hash [false,true]]),
     ("wrong answer replacement port",wrongAnswerPort p,endpoint 2 39 badAnswer 147 [.hash [false,true]]),
     ("wrong raw query port",wrongQueryPort p,endpoint 2 39 fixtureWords 129
       [.hash [true,true,false,false,true,false]]),
     ("corrupt private work storage",corruptStorage 0 p,endpoint 2 39 badWork 126 [.hash [false,true]]),
     ("leave scratch",corruptStorage 7 p,endpoint 2 39 badScratch 126 [.hash [false,true]])]
  for (name,mutant,target) in mutants do
    let actual := observe mutant fixtureHeads fixtureBefore fixtureAfter a b [false,true,true] false
    unless same actual target do
      throw (IO.userError s!"FAIL ROUNDTRIP: independent full mutant endpoint {name}")
    if same actual original then throw (IO.userError s!"FAIL ROUNDTRIP: undetected mutation {name}")
  unless cases.length = 6480 do throw (IO.userError s!"FAIL ROUNDTRIP: count {cases.length}")
  for (h,before,after,a,b,toggle,reply,coin) in cases do
    unless same (observe (NativeRoundTrip.code (native toggle)) h before after a b reply coin)
        (expected toggle h before after a b reply coin) do
      throw (IO.userError s!"FAIL ROUNDTRIP: heads={h 0},{h 1},{h 2},query={before 1}/{after 1},reply={reply},coin={coin}")
  IO.println "PASS ROUNDTRIP: 6480 enumerated +1 directed originals,6 actual code mutants; complete10stacks/threeheads/original livecontinuation/exactevent+charge; zero discards. Storage family is3 distinct fixtures, not fullCartesian all tape lists."

end RoundTrip

end ExplainableCrypto.Helios.Computational.NativeRoundTripGate
