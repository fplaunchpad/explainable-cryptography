import ExplainableCrypto.Helios.Symbolic.SourceInterpretationEnvironment

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

/-- Input keeps exactly its evaluated recipe. An atomic output retains its
environment value modulo full E, with an actual complete emitted message. -/
def FreeLabel.RealizedStep (env : V → Ground) (l : FreeLabel V) (p q : Agent Empty) : Prop :=
  match l with
  | .input c m => Agent.Visible p (.input c (m.subst env)) q
  | .output c x => ∃ m, EqE (env x) m ∧ Agent.Visible p (.output c m) q

theorem FreeLabel.RealizedStep.parLeft {env : V → Ground} {l : FreeLabel V}
    {p q : Agent Empty} (h : l.RealizedStep env p q) (r : Agent Empty) :
    l.RealizedStep env (.par p r) (.par q r) := by
  cases l with
  | input => exact Agent.Visible.parLeft h r
  | output => obtain ⟨m,hm,h⟩ := h; exact ⟨m,hm,Agent.Visible.parLeft h r⟩

theorem FreeLabel.RealizedStep.parRight {env : V → Ground} {l : FreeLabel V}
    {p q : Agent Empty} (h : l.RealizedStep env p q) (r : Agent Empty) :
    l.RealizedStep env (.par r p) (.par r q) := by
  cases l with
  | input => exact Agent.Visible.parRight r h
  | output => obtain ⟨m,hm,h⟩ := h; exact ⟨m,hm,Agent.Visible.parRight r h⟩

theorem FreeLabel.RealizedStep.transport {env : V → Ground} {l : FreeLabel V}
    {p q p' : Agent Empty} (h : l.RealizedStep env p q) (he : Agent.EvalEq p p') :
    ∃ q', l.RealizedStep env p' q' ∧ Agent.EvalEq q q' := by
  cases l with
  | input c m => exact he.input_transport h (.refl _)
  | output c x =>
    obtain ⟨m,hm,h⟩ := h
    obtain ⟨l',q',hq,hl,he'⟩ := he.visible_transport h
    cases hl with
    | output _ hn => exact ⟨q',⟨_,hm.trans hn,hq⟩,he'⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
