import ExplainableCrypto.Helios.Symbolic.SourceInternalCorrespondence

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent

/-- Ground payload events inside the operational presentation. Public output
labels will instead bind a fresh frame handle; they do not reveal this term. -/
inductive PayloadEvent where
  | input : Nat → Ground → PayloadEvent
  | output : Nat → Ground → PayloadEvent

def PayloadEvent.channel : PayloadEvent → Nat
  | .input c _ | .output c _ => c

/-- Direct finite-agent visible rules before parallel structural closure. -/
inductive CoreVisible : Agent Empty → PayloadEvent → Agent Empty → Prop where
  | input (c : Nat) (m : Ground) (body : Agent (Option Empty)) :
      CoreVisible (.input c body) (.input c m) (body.bind m)
  | output (c : Nat) (m : Ground) (p : Agent Empty) :
      CoreVisible (.output c m p) (.output c m) p
  | parLeft {p q : Agent Empty} {a : PayloadEvent} (r : Agent Empty) (h : CoreVisible p a q) :
      CoreVisible (.par p r) a (.par q r)
  | parRight (r : Agent Empty) {p q : Agent Empty} {a : PayloadEvent} (h : CoreVisible p a q) :
      CoreVisible (.par r p) a (.par r q)

def Visible (p : Agent Empty) (a : PayloadEvent) (q : Agent Empty) : Prop :=
  ∃ p' q', ParEq p p' ∧ CoreVisible p' a q' ∧ ParEq q' q

inductive PrimitiveVisible : Agent Empty → PayloadEvent → Agent Empty → Prop where
  | input (c : Nat) (m : Ground) (body : Agent (Option Empty)) :
      PrimitiveVisible (.input c body) (.input c m) (body.bind m)
  | output (c : Nat) (m : Ground) (p : Agent Empty) :
      PrimitiveVisible (.output c m p) (.output c m) p

def VisibleThreads (before : Multiset (Agent Empty)) (a : PayloadEvent)
    (after : Multiset (Agent Empty)) : Prop :=
  ∃ p q context : Agent Empty, PrimitiveVisible p a q ∧
    before=p.threads+context.threads ∧ after=q.threads+context.threads
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
