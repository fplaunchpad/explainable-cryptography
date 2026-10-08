import ExplainableCrypto.Helios.Symbolic.SourcePublicInputPrefixes

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- Actual emitted expressions at every stage, with the currently available
handle domain. Partials and results retain their source projections. -/
def sourceView (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty) :
    (p : Process.Phase) → Frame ns.restricted p.handles
  | .start | .firstReceived =>
    (frame ns swap left right).derive (fun i : Fin 1 => .var (Fin.castLE (by decide) i))
  | .firstPublished | .secondReceived =>
    (frame ns swap left right).derive (fun i : Fin 2 => .var (Fin.castLE (by decide) i))
  | .resultReady rs => sourcePartialFrame ns swap left right rs
  | .done rs => sourceFinalFrame ns swap left right rs
  | .input _ | .check _ _ | .rejected _ | .sendTally _ | .trusteeReply _ | .partialReady _ =>
    frame ns swap left right

def sourceState (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (p : Process.Phase) : ScopedState ns.restricted p.handles :=
  ⟨sourceView ns swap left right p,residual ns swap left right extra ch p⟩

/-- Source and canonical views agree modulo E at every handle, before any
reachability or acceptance assumption is used. -/
theorem source_view_pointwise (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (p : Process.Phase) (i : Fin p.handles) :
    EqE ((sourceView ns swap left right p).value i) ((Process.view ns swap left right p).value i) := by
  cases p with
  | resultReady rs => exact source_partial_pointwise ns swap left right rs i
  | done rs => exact source_final_pointwise ns swap left right rs i
  | _ => exact .refl _

/-- B7/B8 cover the actual expressions in every reached public frame. -/
theorem reachable_source_view_staticEq {ns : Names n} (hf : ns.Fresh)
    {left right : CandidateSubstitution n Empty} {extra : Nat} {p : Process.Phase}
    (h : Process.Reachable ns false left right extra p) :
    Frame.StaticEq (sourceView ns false left right p) (sourceView ns true left right p) :=
  (Frame.staticEq_of_pointwise (source_view_pointwise ns false left right p)).trans
    ((Process.reachable_view_staticEq hf h).trans
      (Frame.staticEq_of_pointwise (source_view_pointwise ns true left right p)).symm)

/-- Capture is literal equality, not merely static equivalence. Heterogeneous
equality records the stage-dependent handle count without erasing its index. -/
theorem Publication.capture {ns : Names n} {swap : Bool} {left right : CandidateSubstitution n Empty}
    {extra handle : Nat} {p q : Process.Phase} {m : Ground}
    (h : Publication ns swap left right extra p handle m q) :
    HEq ((sourceView ns swap left right p).extend m) (sourceView ns swap left right q) := by
  cases h with
  | first =>
    apply heq_of_eq
    change Frame.mk _ = Frame.mk _
    congr 1
    funext i
    fin_cases i <;> rfl
  | second =>
    cases extra <;> apply heq_of_eq <;> change Frame.mk _ = Frame.mk _
    all_goals congr 1; funext i; fin_cases i <;> rfl
  | partials => rfl
  | results => rfl

/-- Every stage publication runs as a fresh-handle output in the evaluated
wrapper and captures exactly the actual next frame. -/
theorem Publication.scoped {ns : Names n} {swap : Bool} {left right : CandidateSubstitution n Empty}
    {extra handle : Nat} {p q : Process.Phase} {m : Ground}
    (h : Publication ns swap left right extra p handle m q) (ch : Channels) (hc : ch.Fresh) :
    ScopedStep ch.privateChannels ns.restricted (sourceState ns swap left right extra ch p)
      (.output ch.broadcast)
      ⟨(sourceView ns swap left right p).extend m,residual ns swap left right extra ch q⟩ ∧
    HEq ((sourceView ns swap left right p).extend m) (sourceView ns swap left right q) :=
  ⟨.output _ _ _ (Channels.broadcast_public hc) (h.visible ch),h.capture⟩
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
