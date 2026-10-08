import ExplainableCrypto.Helios.Computational.NativeWordCompiler
import ExplainableCrypto.Helios.Computational.NativeAdaptiveProbe

/-! Bounded generated-code experiment. Oracle: independently specified six-stack
endpoint, event order and arithmetic charge, not the source evaluator. Enumerate
810 short-input/reply/coin/private-frame cases, plus long/empty literals and four
actual source-code mutations passed through the unchanged compiler. The claim is
only the dense-word path of this fixed probe; unsupported blank-cell moves are
not covered. A mismatched full endpoint, event word/order, or charge refutes it. -/
namespace ExplainableCrypto.Helios.Computational.NativeAdaptiveCompilerGate
open OracleComp OracleSpec

private def handler (firstReply secondReply : List Bool) (coin : Bool) :
    QueryImpl BitOracleMachine.spec (StateT (List BitOracleMachine.Request) Id) :=
  fun q log => match q with
    | .coin => (coin,log++[q])
    | .hash _ => (if log = [] then firstReply else secondReply,log++[q])

def observe (program : NativeOracleTape.Code 9) (before work input oldAnswer
    firstReply secondReply : List Bool) (coin : Bool) :=
  (simulateQ (handler firstReply secondReply coin)
    (BitOracleMachine.run (NativeWordCompiler.code program) 19
      (NativeWordCompiler.start 0 ![before,work,[],input,[],oldAnswer]))).run []

/-- Independent expected complete state and explicit oracle event log. -/
def expected (before work input oldAnswer firstReply secondReply : List Bool)
    (coin : Bool) :=
  let dependent := [firstReply.headD false,coin] ++ input.drop 2
  (((⟨none,0,![before,work,[],dependent,[],secondReply]⟩ : NativeWordCompiler.Config 9),
    66+input.length+dependent.length+oldAnswer.length+2*firstReply.length+secondReply.length),
    [BitOracleMachine.Request.hash input,.coin,.hash dependent])

private def same
    (actual target : (NativeWordCompiler.Config 9 × Nat) × List BitOracleMachine.Request) : Bool :=
  decide (actual.1.1.l = target.1.1.l) && decide (actual.1.1.var = target.1.1.var) &&
    (List.finRange 6).all (fun i => decide (actual.1.1.stk i = target.1.1.stk i)) &&
    decide (actual.1.2 = target.1.2) && decide (actual.2 = target.2)

private def agrees (program : NativeOracleTape.Code 9)
    (before work input oldAnswer firstReply secondReply : List Bool) (coin : Bool) : Bool :=
  same (observe program before work input oldAnswer firstReply secondReply coin)
    (expected before work input oldAnswer firstReply secondReply coin)

private def mutantExpected (work dependent : List Bool) (charge : Nat) :
    (NativeWordCompiler.Config 9 × Nat) × List BitOracleMachine.Request :=
  ((⟨none,0, ![[true,false],work,[],dependent,[],[false,true,false]]⟩,charge),
    [.hash [false,true,true,false,true],.coin,.hash dependent])

private def words : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => [] :: ((words n).flatMap fun w => [false::w,true::w])

private def frames : List (List Bool × List Bool) :=
  [([],[]),([true,false],[false,true,true]),([false,true,false],[true,false])]

private def cases : List (List Bool × List Bool × List Bool × Bool × (List Bool × List Bool)) := do
  let input ← words 3
  let first ← words 1
  let second ← words 1
  let coin ← [false,true]
  let frame ← frames
  pure (input,first,second,coin,frame)

#eval show IO Unit from do
  let old := [true,false,true]
  unless agrees NativeAdaptiveProbe.code [true,false] [false,true,true]
      [false,true,true,false,true] old [true,false] [false,true,false] false do
    throw (IO.userError "FAIL: directed true full state/events/charge")
  unless agrees NativeAdaptiveProbe.code [true,false] [false,true,true]
      [true,false,true] old [false,true] [true] true do
    throw (IO.userError "FAIL: directed false full state/events/charge")
  unless agrees NativeAdaptiveProbe.code [true,false] [false,true,true]
      [] old [] [] true do
    throw (IO.userError "FAIL: empty full state/events/charge")
  let muts : List (String × NativeOracleTape.Code 9 ×
      ((NativeWordCompiler.Config 9 × Nat) × List BitOracleMachine.Request)) := [("wrong work head",NativeAdaptiveProbe.wrongHead,
      mutantExpected [false,true,true] [false,true,true,false,true] 86),
    ("lost branch",NativeAdaptiveProbe.lostBranch,
      mutantExpected [false,true,true] [false,true,true,false,true] 84),
    ("lost coin",NativeAdaptiveProbe.lostCoinDependence,
      mutantExpected [false,true,true] [true,false,true,false,true] 86),
    ("corrupt work",NativeAdaptiveProbe.corruptWork,
      mutantExpected [true,true,true] [true,true,true,false,true] 88)]
  for (name,mutant,mutExpected) in muts do
    let actual := observe mutant [true,false] [false,true,true] [false,true,true,false,true]
      old [true,false] [false,true,false] true
    unless same actual mutExpected do
      throw (IO.userError s!"FAIL: independently expected mutant full state {name}")
    if agrees mutant [true,false] [false,true,true] [false,true,true,false,true]
        old [true,false] [false,true,false] true then
      throw (IO.userError s!"FAIL: undetected compiled source mutant {name}")
  unless cases.length = 810 do
    throw (IO.userError s!"FAIL: fixture count {cases.length}")
  for (input,first,second,coin,(before,work)) in cases do
    unless agrees NativeAdaptiveProbe.code before work input old first second coin do
      throw (IO.userError s!"FAIL: input={input}, first={first}, second={second}, coin={coin}, before={before}, work={work}")
  IO.println "PASS: 810 exhaustive originals + 3 directed originals + 4 compiled actual-source mutations; complete six-stack state, memory/label, event order/words, exact charge; zero discards."

end ExplainableCrypto.Helios.Computational.NativeAdaptiveCompilerGate
