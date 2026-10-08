import ExplainableCrypto.Helios.Computational.NativeOracleTape
import VCVio.OracleComp.SimSemantics.StateT.Basic

/-! Fixed adaptive native source for the bounded compiler experiment.
Candidate: its exact three-event tree is hash input, coin, then hash
[first reply's leading bit, coin] ++ input.drop 2. All work cells survive.
Falsifiers: replying true versus false does not change the second request;
a coin does not change it; work aliases the replaced answer; any final cell
or event order differs. Controls below use independent literal expectations.
No target code or compiler correspondence is assumed in this source probe. -/
namespace ExplainableCrypto.Helios.Computational.NativeAdaptiveProbe
open Turing OracleComp OracleSpec NativeOracleTape
open OracleTapeOutput (wordTape)
set_option maxHeartbeats 500000
set_option maxRecDepth 32768

/-- Literal finite label/current-cell transition table. Only the answer head
is inspected; the independent work tape receives no primitive action. -/
def code : Code 9 := fun l h =>
  if l = 0 then .oracle .hash 1
  else if l = 1 then
    if h 2 = some true then .local 2 ![none,some (.write (some true)),none]
    else .local 3 ![none,some (.write (some false)),none]
  else if l = 2 ∨ l = 3 then .local 4 ![none,some (.move .right),none]
  else if l = 4 then .oracle .coin 5
  else if l = 5 then .local 6 ![none,some (.write (some (h 2 == some true))),none]
  else if l = 6 then .local 7 ![none,some (.move .left),none]
  else if l = 7 then .oracle .hash 8
  else .halt

def start (work oldAnswer : Tape Cell) (input : List Bool) : Config 9 :=
  ⟨some 0,work,wordTape input,oldAnswer⟩

def branchBit (firstReply : List Bool) : Bool := firstReply.headD false

def dependentWord (input firstReply : List Bool) (coin : Bool) : List Bool :=
  [branchBit firstReply,coin] ++ input.drop 2

def result (work : Tape Cell) (input firstReply : List Bool) (coin : Bool)
    (secondReply : List Bool) : Config 9 :=
  ⟨none,work,wordTape (dependentWord input firstReply coin),wordTape secondReply⟩

def expected (work : Tape Cell) (input : List Bool) : OracleComp BitOracleMachine.spec (Config 9) := do
  let firstReply ← liftM (BitOracleMachine.spec.query (.hash input))
  let coin ← liftM (BitOracleMachine.spec.query .coin)
  let secondReply ← liftM (BitOracleMachine.spec.query (.hash (dependentWord input firstReply coin)))
  pure (result work input firstReply coin secondReply)

private def handler (firstReply secondReply : List Bool) (coin : Bool) :
    QueryImpl BitOracleMachine.spec (StateT (List BitOracleMachine.Request) Id) :=
  fun q log => match q with
    | .coin => (coin,log++[q])
    | .hash _ => (if log = [] then firstReply else secondReply,log++[q])

/-- Nonempty private cells on both sides of the initial head. -/
def controlWork : Tape Cell :=
  Tape.mk' (ListBlank.mk [some true,some false])
    (ListBlank.mk [some false,some true,some true])

def observe (program : Code 9) (input firstReply secondReply : List Bool) (coin : Bool) :=
  (simulateQ (handler firstReply secondReply coin)
    (run program 9 (start controlWork ((wordTape [true,false,true]).move .right) input))).run []

/-- Independent full-state and event-log fixture: all three words differ and
nonpalindromic input suffix survives the two writes. -/
theorem positive_true : observe code [false,true,true,false,true]
    [true,false] [false,true,false] false =
    ((⟨none,controlWork,wordTape [true,false,true,false,true],
      wordTape [false,true,false]⟩ : Config 9),
      [.hash [false,true,true,false,true],.coin,.hash [true,false,true,false,true]]) := by
  rfl

theorem positive_false : observe code [true,false,true] [false,true] [true] true =
    ((⟨none,controlWork,wordTape [false,true,true],wordTape [true]⟩ : Config 9),
      [.hash [true,false,true],.coin,.hash [false,true,true]]) := by
  rfl

theorem positive_empty : observe code [] [] [] true =
    ((⟨none,controlWork,wordTape [false,true],wordTape []⟩ : Config 9),
      [.hash [],.coin,.hash [false,true]]) := by
  rfl

/-- Actual instruction mutants, retaining all other original commands. -/
def wrongHead : Code 9 := fun l h => if l = 1 then
  .local 2 ![none,some (.write (some (h 0 == some true))),none] else code l h

def lostBranch : Code 9 := fun l h => if l = 1 then
  .local 2 ![none,none,none] else code l h

def lostCoinDependence : Code 9 := fun l h => if l = 5 then
  .local 6 ![none,some (.write (some false)),none] else code l h

def corruptWork : Code 9 := fun l h => if l = 1 then
  .local 2 ![some (.write (h 2)),some (.write (some true)),none] else code l h

theorem wrong_head_detected :
    (observe wrongHead [false,true,true,false,true] [true,false] [false,true,false] false).2 ≠
      [.hash [false,true,true,false,true],.coin,.hash [true,false,true,false,true]] := by decide +kernel

theorem lost_branch_detected :
    (observe lostBranch [false,true,true,false,true] [true,false] [false,true,false] false).2 ≠
      [.hash [false,true,true,false,true],.coin,.hash [true,false,true,false,true]] := by decide +kernel

theorem lost_coin_dependence_detected :
    (observe lostCoinDependence [true,false,true] [false,true] [true] true).2 ≠
      [.hash [true,false,true],.coin,.hash [false,true,true]] := by decide +kernel

theorem corrupt_work_detected :
    (observe corruptWork [false,true,true,false,true] [true,false] [false,true,false] false).1.work.head ≠
      controlWork.head := by decide +kernel


private def beforeCoin (work : Tape Cell) (input firstReply : List Bool) : Config 9 :=
  ⟨some 4,work,((wordTape input).write (some (branchBit firstReply))).move .right,
    wordTape firstReply⟩

private def afterCoin (work : Tape Cell) (input firstReply : List Bool) (coin : Bool) : Config 9 :=
  ⟨some 5,work,((wordTape input).write (some (branchBit firstReply))).move .right,
    wordTape [coin]⟩

private def beforeHash (work : Tape Cell) (input firstReply : List Bool) (coin : Bool) : Config 9 :=
  ⟨some 7,work,wordTape (dependentWord input firstReply coin),wordTape [coin]⟩

private theorem branch_run (work : Tape Cell) (input firstReply : List Bool) :
    run code 2 (⟨some 1,work,wordTape input,wordTape firstReply⟩ : Config 9) =
      pure (beforeCoin work input firstReply) := by
  cases firstReply with
  | nil => rfl
  | cons b rest => cases b <;> rfl

private theorem query_writes (input : List Bool) (b coin : Bool) :
    ((((wordTape input).write (some b)).move .right).write (some coin)).move .left =
      wordTape ([b,coin] ++ input.drop 2) := by
  cases input with
  | nil => rfl
  | cons a rest => cases rest <;> rfl

private theorem dependent_run (work : Tape Cell) (input firstReply : List Bool) (coin : Bool) :
    run code 2 (afterCoin work input firstReply coin) =
      pure (beforeHash work input firstReply coin) := by
  have he : run code 2 (afterCoin work input firstReply coin) =
      (pure (⟨some 7,work,
        ((((wordTape input).write (some (branchBit firstReply))).move .right).write (some coin)).move .left,
        wordTape [coin]⟩ : Config 9) : OracleComp BitOracleMachine.spec (Config 9)) := by
    cases coin <;> rfl
  rw [he,query_writes]
  rfl

/-- Exact native query tree and complete terminal tapes. Replies and the old
answer/work tapes are arbitrary; bounded replies need no additional proof. -/
theorem exact_run (work oldAnswer : Tape Cell) (input : List Bool) :
    run code 8 (start work oldAnswer input) = expected work input := by
  have hfirst := hash_step code (start work oldAnswer input) 0 1 rfl (by rfl)
  let H : List Bool → OracleComp BitOracleMachine.spec (Config 9) := fun query => do
    let answer ← liftM (BitOracleMachine.spec.query (.hash query))
    pure ⟨some 1,work,wordTape input,wordTape answer⟩
  change step code (start work oldAnswer input) = H (OracleTapeDispatch.readWord (wordTape input)) at hfirst
  rw [OracleTapeDispatch.read_wordTape] at hfirst
  rw [run,hfirst]
  simp only [H,bind_assoc,pure_bind]
  unfold expected
  refine bind_congr (fun (a : List Bool) => ?_)
  rw [show 7 = 2+5 by decide,run_add,branch_run,pure_bind]
  have hc := coin_step code (beforeCoin work input a) 4 5 rfl (by rfl)
  rw [run,hc]
  simp only [bind_assoc,pure_bind]
  refine bind_congr (fun (coin : Bool) => ?_)
  change run code 4 (afterCoin work input a coin) = _
  rw [show 4 = 2+2 by decide,run_add,dependent_run,pure_bind]
  have hh := hash_step code (beforeHash work input a coin) 7 8 rfl (by rfl)
  let H2 : List Bool → OracleComp BitOracleMachine.spec (Config 9) := fun query => do
    let answer ← liftM (BitOracleMachine.spec.query (.hash query))
    pure ⟨some 8,work,wordTape (dependentWord input a coin),wordTape answer⟩
  change step code (beforeHash work input a coin) = H2
    (OracleTapeDispatch.readWord (wordTape (dependentWord input a coin))) at hh
  rw [OracleTapeDispatch.read_wordTape] at hh
  rw [run,hh]
  simp only [H2,bind_assoc,pure_bind]
  refine bind_congr (fun (answer : List Bool) => ?_)
  rfl

/-- The frozen nine-step validation clock adds one absorbing halt step. -/
theorem padded_run (work oldAnswer : Tape Cell) (input : List Bool) :
    run code 9 (start work oldAnswer input) = expected work input := by
  change run code (8+1) (start work oldAnswer input) = _
  rw [run_add,exact_run]
  simp [expected,bind_assoc,result,run,step]

/-- Dense finite half-tapes, with the nearest cell first on each side. -/
def zipTape (before right : List Bool) : Tape Cell :=
  Tape.mk' (ListBlank.mk (before.map some)) (ListBlank.mk (right.map some))

theorem zipTape_word (right : List Bool) : zipTape [] right = wordTape right := rfl

theorem zipTape_right (before rest : List Bool) (b : Bool) :
    (zipTape before (b::rest)).move .right = zipTape (b::before) rest := rfl

theorem zipTape_left (before right : List Bool) (b : Bool) :
    (zipTape (b::before) right).move .left = zipTape before (b::right) := by
  simp only [zipTape,Tape.move_left_mk']
  rfl

theorem zipTape_write (before right : List Bool) (b : Bool) :
    (zipTape before right).write (some b) = zipTape before (b::right.tail) := by
  cases right <;> rfl

end ExplainableCrypto.Helios.Computational.NativeAdaptiveProbe
