import ExplainableCrypto.Helios.Symbolic.SourceScopedActions

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

theorem residual_publishFirst (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) :
    Agent.Visible (residual ns swap left right extra ch .firstReceived)
      (.output ch.broadcast (ballot ns 0 (choice swap left right 0).value))
      (residual ns swap left right extra ch .firstPublished) := by
  exact Agent.Visible.of_core (.parRight _ (.parLeft _ (.output _ _ _)))

theorem residual_publishSecond (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) :
    Agent.Visible (residual ns swap left right extra ch .secondReceived)
      (.output ch.broadcast (ballot ns 1 (choice swap left right 1).value))
      (residual ns swap left right extra ch (Process.afterAccepted extra [])) := by
  rw [residual_afterAccepted]
  simp only [residual,List.length_nil,Nat.sub_zero]
  exact Agent.Visible.of_core (.parLeft _ (.output _ _ _))

theorem residual_publishPartial (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (rs : List (Recipe 3)) :
    Agent.Visible (residual ns swap left right extra ch (.partialReady rs))
      (.output ch.broadcast (sourcePartials ns swap left right rs))
      (residual ns swap left right extra ch (.resultReady rs)) :=
  Agent.Visible.of_core (.output _ _ _)

theorem residual_publishResult (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (rs : List (Recipe 3)) :
    Agent.Visible (residual ns swap left right extra ch (.resultReady rs))
      (.output ch.broadcast (sourceResults ns swap left right rs))
      (residual ns swap left right extra ch (.done rs)) :=
  Agent.Visible.of_core (.output _ _ _)

/-- A public voter input reaches the literal pending guard and retains the
waiting trustee. Acceptance is a subsequent Tau, not an input premise. -/
theorem residual_visible_input (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (rs : List (Recipe 3)) (r : Recipe 3) (hr : rs.length < extra) :
    Agent.Visible (residual ns swap left right extra ch (.input rs))
      (.input (ch.voter (rs.length+2)) ((frame ns swap left right).eval r))
      (residual ns swap left right extra ch (.check rs r)) := by
  let first := ballot ns 0 (choice swap left right 0).value
  let second := ballot ns 1 (choice swap left right 1).value
  let others := receivedBallots ns swap left right rs
  let body : Agent (Option Empty) := .branch
    (electionGuard n (shiftTerm (publicKey ns)) (shiftTerm first :: shiftTerm second :: others.map shiftTerm) (.var none))
    (collectBallots n ch (extra-(rs.length+1)) (shiftTerm (publicKey ns)) (shiftTerm first) (shiftTerm second)
      (others.map shiftTerm ++ [.var none])) .nil
  have he : extra-rs.length=(extra-(rs.length+1))+1 := by omega
  have h := Agent.Visible.of_core (Agent.CoreVisible.parLeft (trusteeAgent (n := n) ch (.name ns.secretKey))
    (Agent.CoreVisible.input (ch.voter (rs.length+2)) ((frame ns swap left right).eval r) body))
  dsimp only [residual]
  rw [he,collectBallots]
  simpa only [body,first,second,others,collectBallots_bind,receivedBallots,
    List.length_map,List.map_append,List.map_singleton] using h

/-- The actual input frame is unchanged, and the label's recipe is restricted
to the current three public handles and public literal names. -/
theorem residual_scoped_input (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (hc : ch.Fresh) (rs : List (Recipe 3)) (r : Recipe 3)
    (hrange : rs.length < extra) (hr : r.Public ns.restricted) :
    ScopedStep ch.privateChannels ns.restricted
      ⟨frame ns swap left right,residual ns swap left right extra ch (.input rs)⟩
      (.input (ch.voter (rs.length+2)) r)
      ⟨frame ns swap left right,residual ns swap left right extra ch (.check rs r)⟩ := by
  exact .input _ _ _ ((Channels.voter_public_iff hc _).mpr (by omega)) hr
    (residual_visible_input ns swap left right extra ch rs r hrange)

/-- The rejected trustee remains as an input process, but the fixed private
restriction prevents every public action; internal quiescence was proved earlier.
This closes that behavior in the evaluated wrapper, not arbitrary source scope. -/
theorem rejected_no_scoped_step (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (rs : List (Recipe 3)) {handles after : Nat}
    (φ : Frame ns.restricted handles) (a : PublicEvent handles after) (q : ScopedState ns.restricted after) :
    ¬ ScopedStep ch.privateChannels ns.restricted
      ⟨φ,residual ns swap left right extra ch (.rejected rs)⟩ a q := by
  intro h
  cases a with
  | tau =>
    have ht := ((scoped_tau_iff _ _).mp h).2
    exact residual_rejected_no_tau ns swap left right extra ch rs _ ht
  | input c r =>
    obtain ⟨hc,_,_,hv⟩ := (scoped_input_iff _ _ _ _).mp h
    obtain ⟨body,hm⟩ := hv.input_prefix
    simp only [residual,trusteeAgent,Agent.threads,Agent.threadList,Multiset.mem_coe,
      List.mem_singleton,Agent.input.injEq] at hm
    exact hc (hm.1 ▸ Channels.trustee_private ch)
  | output c =>
    obtain ⟨_,m,_,hv⟩ := (scoped_output_iff _ _ _).mp h
    obtain ⟨body,hm⟩ := hv.output_prefix
    simp [residual,trusteeAgent,Agent.threads,Agent.threadList] at hm
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
