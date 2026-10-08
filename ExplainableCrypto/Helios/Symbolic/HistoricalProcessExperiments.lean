import ExplainableCrypto.Helios.Symbolic.HistoricalProcessSyntax
import ExplainableCrypto.Helios.Symbolic.ElectionTallyExperiments

namespace ExplainableCrypto.Helios.Symbolic.HistoricalProcessExperiments
open ExplainableCrypto.Testing Historical General Process

/-- Directed fixture oracle for literal one-candidate ballots. Raw normalization
is not an E decision procedure; general transition matching is proved separately. -/
private def acceptedRaw (swap : Bool) (rs : List (Recipe 3)) (r : Recipe 3) : Bool :=
  let ns := ProofObservationSPOT.oneNames
  let φ := frame ns swap ProofObservationSPOT.oneLeft ProofObservationSPOT.oneRight
  let b := φ.eval r
  normalizeRaw (.ternary .checkspk (publicKey ns) (b.project 0) (b.project 1)) == .const .ok &&
  normalizeRaw (.ternary .checkspk (publicKey ns) (b.project 0) (b.project 2)) == .const .ok &&
  normalizeRaw (b.drop 3) == .const .bottom &&
  (honestBoardRecipes++rs).all (fun s => normalizeRaw ((φ.eval s).project 0) != normalizeRaw (b.project 0))

private def submission (badAt seed i : Nat) : Recipe 3 :=
  if i=badAt then .var 1 else ElectionTallyExperiments.publicBallot (40+i)
    (if (seed+i)%2=0 then .zero else .one)

-- Local executable mirror, with one mutation switch used only by this gate.
private def advance (mutation : Nat) (swap : Bool) (extra badAt seed : Nat) : Phase → Option (Action × Phase)
  | .start => some (.tau,.firstReceived)
  | .firstReceived => some (.output 1,.firstPublished)
  | .firstPublished => some (.tau,.secondReceived)
  | .secondReceived => some (.output 2,afterAccepted extra [])
  | .input rs => if rs.length < extra then
      some (.input (if mutation=3 then 2 else rs.length+2) (submission badAt seed rs.length),
        .check rs (submission badAt seed rs.length)) else none
  | .check rs r => some (.tau,if mutation=1 || acceptedRaw swap rs r then
      afterAccepted extra (rs++[r]) else .rejected rs)
  | .rejected _ | .done _ => none
  | .sendTally rs => some (.tau,.trusteeReply rs)
  | .trusteeReply rs => some (.tau,.partialReady rs)
  | .partialReady rs => some (.output (if mutation=2 then 4 else 3),.resultReady rs)
  | .resultReady rs => some (.output 4,.done rs)

private def trace (mutation : Nat) (swap : Bool) (extra badAt seed : Nat) : Nat → Phase → List Action × Phase × Bool
  | 0,p => ([],p,true)
  | fuel+1,p => match advance mutation swap extra badAt seed p with
    | none => ([],p,true)
    | some (a,q) =>
      let rest := trace mutation swap extra badAt seed fuel q
      let domainOk := match a with
        | .output h => h == p.handles && q.handles == p.handles+1
        | .input _ _ => p.handles == 3 && q.handles == 3
        | .tau => p.handles == q.handles
      (a::rest.1,rest.2.1,domainOk && rest.2.2)

private def expected (extra badAt seed : Nat) : List Action :=
  [.tau,.output 1,.tau,.output 2] ++
  ((List.range (min extra (badAt+1))).flatMap (fun i =>
    [.input (i+2) (submission badAt seed i),.tau])) ++
  (if badAt < extra then [] else [.tau,.tau,.output 3,.output 4])

private def checkWith (mutation extra badAt seed : Nat) : Bool :=
  [false,true].all fun swap =>
    let out := trace mutation swap extra badAt seed (12+2*extra) .start
    let accepted := (List.range (min extra badAt)).map (submission badAt seed)
    let endpoint := if badAt < extra then Phase.rejected accepted else .done accepted
    decide (out.1=expected extra badAt seed ∧ out.2.1=endpoint) && out.2.2

def check (seed : Nat) : Bool :=
  let extra := seed%6
  checkWith 0 extra extra seed && checkWith 0 extra (seed/6%(extra+1)) seed

def ignoresRejection (_ : Nat) := checkWith 1 1 0 0
def resultsBeforePartials (_ : Nat) := checkWith 2 0 0 0
def wrongVoterChannel (_ : Nat) := checkWith 3 2 2 0
def exposesSecondEarly (_ : Nat) := Phase.firstPublished.handles == 3

#eval campaign "process continues after rejection (negative control)" (∀ n : Nat, ignoresRejection n=true) 1 true
#eval campaign "process publishes result before partial (negative control)" (∀ n : Nat, resultsBeforePartials n=true) 1 true
#eval campaign "process repeats the previous voter channel (negative control)" (∀ n : Nat, wrongVoterChannel n=true) 1 true
#eval campaign "process exposes the second ballot early (negative control)" (∀ n : Nat, exposesSecondEarly n=true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "historical stages preserve source ordering, domains, success and stop-on-rejection"
      (∀ n : Nat, check n=true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "historical process backstop failed")
  IO.println "historical process backstop: 2048 inputs, zero through five extra voters, successful and replay-rejected executions in both swaps"

end ExplainableCrypto.Helios.Symbolic.HistoricalProcessExperiments
