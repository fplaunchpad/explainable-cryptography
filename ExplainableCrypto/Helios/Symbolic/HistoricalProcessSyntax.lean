import ExplainableCrypto.Helios.Symbolic.PublishedStaticEquivalence

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Process

/-- The twelve normalized residuals R1–R12 in the historical source, with
accepted inputs and a pending check retained as syntax. This is a process-stage
model; correspondence to unrestricted applied-pi syntax is a separate theorem. -/
inductive Phase where
  | start
  | firstReceived
  | firstPublished
  | secondReceived
  | input (accepted : List (Recipe 3))
  | check (accepted : List (Recipe 3)) (pending : Recipe 3)
  | rejected (accepted : List (Recipe 3))
  | sendTally (accepted : List (Recipe 3))
  | trusteeReply (accepted : List (Recipe 3))
  | partialReady (accepted : List (Recipe 3))
  | resultReady (accepted : List (Recipe 3))
  | done (accepted : List (Recipe 3))
  deriving DecidableEq

/-- Public output labels bind the next canonical handle on channel c. Input
labels identify the next public voter channel (zero-based voter index >=2)
and the full public recipe. Private handshakes and checks carry tau labels. -/
inductive Action where
  | tau
  | output (handle : Nat)
  | input (voter : Nat) (recipe : Recipe 3)
  deriving DecidableEq

def Phase.history : Phase → List (Recipe 3)
  | .start | .firstReceived | .firstPublished | .secondReceived => []
  | .input rs | .check rs _ | .rejected rs | .sendTally rs | .trusteeReply rs |
    .partialReady rs | .resultReady rs | .done rs => rs

def Phase.handles : Phase → Nat
  | .start | .firstReceived => 1
  | .firstPublished | .secondReceived => 2
  | .resultReady _ => 4
  | .done _ => 5
  | _ => 3

/-- The source counts all eligible voters, including the two honest voters.
After the last successful input (or the second honest output if extra=0),
control goes directly to the private tally send. -/
def afterAccepted (extra : Nat) (rs : List (Recipe 3)) : Phase :=
  if rs.length < extra then .input rs else .sendTally rs

/-- No output from an attacker ballot is added to the public frame: the sender
already knows its recipe. Only honest ballots, partials and results are output. -/
def view {n : Nat} (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) : (p : Phase) → Frame ns.restricted p.handles
  | .start | .firstReceived =>
    (frame ns swap left right).derive (fun i : Fin 1 => .var (Fin.castLE (by decide) i))
  | .firstPublished | .secondReceived =>
    (frame ns swap left right).derive (fun i : Fin 2 => .var (Fin.castLE (by decide) i))
  | .resultReady rs => partialFrame ns swap left right rs
  | .done rs => finalFrame ns swap left right rs
  | .input _ | .check _ _ | .rejected _ | .sendTally _ | .trusteeReply _ | .partialReady _ =>
    frame ns swap left right

/-- The exact corrected public ballot check on the accumulated board. -/
def accepts {n : Nat} (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (r : Recipe 3) : Prop :=
  Accepted n (publicKey ns) ((honestBoardRecipes ++ rs).map (frame ns swap left right).eval)
    ((frame ns swap left right).eval r)

/-- Exact control transitions for the normalized source stages. No acceptance
premise occurs on an input; its success/failure is a subsequent internal step.
Rejected and completed phases have no outgoing transitions. -/
inductive Step {n : Nat} (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) : Phase → Action → Phase → Prop where
  | receiveFirst : Step ns swap left right extra .start .tau .firstReceived
  | publishFirst : Step ns swap left right extra .firstReceived (.output 1) .firstPublished
  | receiveSecond : Step ns swap left right extra .firstPublished .tau .secondReceived
  | publishSecond : Step ns swap left right extra .secondReceived (.output 2) (afterAccepted extra [])
  | input {rs r} (hroom : rs.length < extra) (hr : r.Public ns.restricted) :
      Step ns swap left right extra (.input rs) (.input (rs.length+2) r) (.check rs r)
  | accept {rs r} (ha : accepts ns swap left right rs r) :
      Step ns swap left right extra (.check rs r) .tau (afterAccepted extra (rs++[r]))
  | reject {rs r} (ha : ¬ accepts ns swap left right rs r) :
      Step ns swap left right extra (.check rs r) .tau (.rejected rs)
  | sendTally {rs} : Step ns swap left right extra (.sendTally rs) .tau (.trusteeReply rs)
  | receivePartial {rs} : Step ns swap left right extra (.trusteeReply rs) .tau (.partialReady rs)
  | publishPartial {rs} : Step ns swap left right extra (.partialReady rs) (.output 3) (.resultReady rs)
  | publishResult {rs} : Step ns swap left right extra (.resultReady rs) (.output 4) (.done rs)

/-- All steps, including visible ones; reflexive transitive reachability does
not constrain the adversary to a predetermined input list or strategy. -/
def Reachable {n : Nat} (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (p : Phase) : Prop :=
  Relation.ReflTransGen (fun p q => ∃ a, Step ns swap left right extra p a q) .start p

end ExplainableCrypto.Helios.Symbolic.Historical.General.Process
