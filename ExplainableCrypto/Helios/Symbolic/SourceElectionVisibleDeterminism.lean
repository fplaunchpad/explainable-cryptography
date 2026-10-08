import ExplainableCrypto.Helios.Symbolic.SourceCanonicalOpeningVisible

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- Every channel has at most one complete active input continuation in any
election residual. This includes private inputs, not only public prefixes. -/
theorem residual_input_unique (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (phase : Process.Phase) (c : Nat) (a b : Agent (Option Empty))
    (ha : Agent.input c a ∈ (residual ns swap left right extra ch phase).threads)
    (hb : Agent.input c b ∈ (residual ns swap left right extra ch phase).threads) : a=b := by
  have ht₀ := hc.trustee_voter 0
  have ht₁ := hc.trustee_voter 1
  cases phase with
  | input rs =>
    cases he : extra-rs.length with
    | zero =>
      simp [residual,he,collectBallots,boardFinish,trusteeAgent,Agent.threads,Agent.threadList] at ha hb
      exact ha.2.trans hb.2.symm
    | succ rem =>
      have ht₂ := hc.trustee_voter (rs.length+2)
      clear hc
      simp [residual,he,collectBallots,trusteeAgent,receivedBallots,Agent.threads,Agent.threadList] at ha hb
      aesop
  | _ =>
    clear hc
    simp [residual,electionBody,boardStart,boardSecond,boardFinish,trusteeAgent,Agent.threads,Agent.threadList] at ha hb
    all_goals aesop

/-- Every channel has at most one complete active output value/continuation,
even when the residual has simultaneous outputs on distinct private channels. -/
theorem residual_output_unique (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (phase : Process.Phase) (c : Nat) (m t : Ground) (a b : Agent Empty)
    (ha : Agent.output c m a ∈ (residual ns swap left right extra ch phase).threads)
    (hb : Agent.output c t b ∈ (residual ns swap left right extra ch phase).threads) : m=t ∧ a=b := by
  have hv := hc.honest_distinct
  have hp := hc.broadcast_voter 1
  cases phase with
  | input rs =>
    cases he : extra-rs.length with
    | zero =>
      simp [residual,he,collectBallots,boardFinish,trusteeAgent,Agent.threads,Agent.threadList] at ha hb
      exact ⟨ha.2.1.trans hb.2.1.symm,ha.2.2.trans hb.2.2.symm⟩
    | succ rem =>
      simp [residual,he,collectBallots,trusteeAgent,Agent.threads,Agent.threadList] at ha
  | _ =>
    clear hc
    simp [residual,electionBody,boardStart,boardSecond,boardFinish,trusteeAgent,Agent.threads,Agent.threadList] at ha hb
    all_goals aesop

theorem residual_visible_input_deterministic (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (phase : Process.Phase) (c : Nat) (m : Ground) (p q : Agent Empty)
    (hp : Agent.Visible (residual ns swap left right extra ch phase) (.input c m) p)
    (hq : Agent.Visible (residual ns swap left right extra ch phase) (.input c m) q) : Agent.EvalEq p q :=
  .of_parEq (Agent.visible_input_deterministic hp hq (residual_input_unique ns swap left right extra ch hc phase c))

theorem residual_visible_output_deterministic (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (phase : Process.Phase) (c : Nat) (m : Ground) (p : Agent Empty) (t : Ground) (q : Agent Empty)
    (hp : Agent.Visible (residual ns swap left right extra ch phase) (.output c m) p)
    (hq : Agent.Visible (residual ns swap left right extra ch phase) (.output c t) q) :
    EqE m t ∧ Agent.EvalEq p q := by
  obtain ⟨a,ha⟩ := hp.output_prefix
  obtain ⟨b,hb⟩ := hq.output_prefix
  obtain ⟨rfl,_⟩ := residual_output_unique ns swap left right extra ch hc phase c m t a b ha hb
  exact ⟨.refl _,.of_parEq (Agent.visible_output_deterministic hp hq
    (fun a b ha hb => (residual_output_unique ns swap left right extra ch hc phase c m m a b ha hb).2))⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
