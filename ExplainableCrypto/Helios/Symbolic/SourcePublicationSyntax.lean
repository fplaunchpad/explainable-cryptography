import ExplainableCrypto.Helios.Symbolic.SourceVisibleInversion

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- A value-retaining adapter for the four stage output constructors. It is
used only to connect the stage's handle label to the literal emitted message. -/
inductive Publication (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) : Process.Phase → Nat → Ground → Process.Phase → Prop where
  | first : Publication ns swap left right extra .firstReceived 1
      (ballot ns 0 (choice swap left right 0).value) .firstPublished
  | second : Publication ns swap left right extra .secondReceived 2
      (ballot ns 1 (choice swap left right 1).value) (Process.afterAccepted extra [])
  | partials {rs} : Publication ns swap left right extra (.partialReady rs) 3
      (sourcePartials ns swap left right rs) (.resultReady rs)
  | results {rs} : Publication ns swap left right extra (.resultReady rs) 4
      (sourceResults ns swap left right rs) (.done rs)

theorem Publication.stage {ns : Names n} {swap : Bool} {left right : CandidateSubstitution n Empty}
    {extra handle : Nat} {p q : Process.Phase} {m : Ground}
    (h : Publication ns swap left right extra p handle m q) :
    Process.Step ns swap left right extra p (.output handle) q := by
  cases h with
  | first => exact .publishFirst
  | second => exact .publishSecond
  | partials => exact .publishPartial
  | results => exact .publishResult

theorem stage_output_publication {ns : Names n} {swap : Bool} {left right : CandidateSubstitution n Empty}
    {extra handle : Nat} {p q : Process.Phase} (h : Process.Step ns swap left right extra p (.output handle) q) :
    ∃ m, Publication ns swap left right extra p handle m q := by
  cases h with
  | publishFirst => exact ⟨_,.first⟩
  | publishSecond => exact ⟨_,.second⟩
  | publishPartial => exact ⟨_,.partials⟩
  | publishResult => exact ⟨_,.results⟩

theorem Publication.visible {ns : Names n} {swap : Bool} {left right : CandidateSubstitution n Empty}
    {extra handle : Nat} {p q : Process.Phase} {m : Ground}
    (h : Publication ns swap left right extra p handle m q) (ch : Channels) :
    Agent.Visible (residual ns swap left right extra ch p) (.output ch.broadcast m)
      (residual ns swap left right extra ch q) := by
  cases h with
  | first => exact residual_publishFirst ns swap left right extra ch
  | second => exact residual_publishSecond ns swap left right extra ch
  | partials => exact residual_publishPartial ns swap left right extra ch _
  | results => exact residual_publishResult ns swap left right extra ch _
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
