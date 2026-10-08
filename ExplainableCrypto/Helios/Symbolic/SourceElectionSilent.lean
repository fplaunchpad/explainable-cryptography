import ExplainableCrypto.Helios.Symbolic.SourceElectionResiduals
import ExplainableCrypto.Helios.Symbolic.SourceParallelGuards

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

theorem residual_receiveFirst (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) :
    Agent.Tau (residual ns swap left right extra ch .start)
      (residual ns swap left right extra ch .firstReceived) := by
  have h := (Agent.Tau.of_core (board_first_communication n extra ch (publicKey ns)
    (ballot ns 0 (choice swap left right 0).value))).parLeft
      (.par (.output (ch.voter 1) (ballot ns 1 (choice swap left right 1).value) .nil)
        (trusteeAgent (n := n) ch (.name ns.secretKey)))
  refine Agent.Tau.congr ?_ h ?_
  all_goals
    apply (Agent.parEq_iff_threads _ _).mpr
    simp only [residual,electionBody,Agent.threads_par,Agent.threads_nil,zero_add,
      add_assoc,add_comm,add_left_comm]

theorem residual_receiveSecond (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) :
    Agent.Tau (residual ns swap left right extra ch .firstPublished)
      (residual ns swap left right extra ch .secondReceived) := by
  have h := (Agent.Tau.of_core (board_second_communication n extra ch (publicKey ns)
    (ballot ns 0 (choice swap left right 0).value) (ballot ns 1 (choice swap left right 1).value))).parLeft
      (trusteeAgent (n := n) ch (.name ns.secretKey))
  refine Agent.Tau.congr ?_ h ?_
  all_goals
    apply (Agent.parEq_iff_threads _ _).mpr
    simp only [residual,receivedBallots,List.map_nil,Agent.threads_par,Agent.threads_nil,
      zero_add,add_assoc]

theorem residual_accept (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (rs : List (Recipe 3)) (r : Recipe 3)
    (ha : Process.accepts ns swap left right rs r) :
    Agent.Tau (residual ns swap left right extra ch (.check rs r))
      (residual ns swap left right extra ch (Process.afterAccepted extra (rs++[r]))) := by
  rw [residual_afterAccepted]
  have h := (Agent.Tau.of_core (collection_accept n (extra-(rs.length+1)) ch (publicKey ns)
    (ballot ns 0 (choice swap left right 0).value) (ballot ns 1 (choice swap left right 1).value)
    ((frame ns swap left right).eval r) (receivedBallots ns swap left right rs)
    ((source_accepts_iff ns swap left right rs r).mp ha))).parLeft
      (trusteeAgent (n := n) ch (.name ns.secretKey))
  simpa only [residual,receivedBallots_append,List.length_append,List.length_singleton] using h

theorem residual_reject (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (rs : List (Recipe 3)) (r : Recipe 3)
    (ha : ¬ Process.accepts ns swap left right rs r) :
    Agent.Tau (residual ns swap left right extra ch (.check rs r))
      (residual ns swap left right extra ch (.rejected rs)) := by
  have h := (Agent.Tau.of_core (collection_reject n (extra-(rs.length+1)) ch (publicKey ns)
    (ballot ns 0 (choice swap left right 0).value) (ballot ns 1 (choice swap left right 1).value)
    ((frame ns swap left right).eval r) (receivedBallots ns swap left right rs)
    (fun h => ha ((source_accepts_iff ns swap left right rs r).mpr h)))).parLeft
      (trusteeAgent (n := n) ch (.name ns.secretKey))
  have hh := Agent.Tau.congr (Agent.ParEq.refl _) h (Agent.ParEq.zero_left _)
  simpa only [residual,receivedBallots_append] using hh

theorem residual_sendTally (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (rs : List (Recipe 3)) :
    Agent.Tau (residual ns swap left right extra ch (.sendTally rs))
      (residual ns swap left right extra ch (.trusteeReply rs)) := by
  exact Agent.Tau.of_core (board_tally_communication ch
    (ballot ns 0 (choice swap left right 0).value) (ballot ns 1 (choice swap left right 1).value)
    (.name ns.secretKey) (receivedBallots ns swap left right rs))

theorem residual_receivePartial (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (rs : List (Recipe 3)) :
    Agent.Tau (residual ns swap left right extra ch (.trusteeReply rs))
      (residual ns swap left right extra ch (.partialReady rs)) := by
  exact Agent.Tau.congr (Agent.ParEq.comm _ _)
    (Agent.Tau.of_core (board_reply_communication ch (sourceTallies ns swap left right rs)
      (sourcePartials ns swap left right rs))) (Agent.ParEq.zero_left _)

/-- Every internal stage transition is realized by the literal finite election
residuals modulo the source parallel laws. Converse classification, restrictions
and visible transitions are not premises hidden in this statement. -/
theorem residual_tau_step (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) {p q : Process.Phase}
    (h : Process.Step ns swap left right extra p .tau q) :
    Agent.Tau (residual ns swap left right extra ch p) (residual ns swap left right extra ch q) := by
  cases h with
  | receiveFirst => exact residual_receiveFirst ns swap left right extra ch
  | receiveSecond => exact residual_receiveSecond ns swap left right extra ch
  | accept ha => exact residual_accept ns swap left right extra ch _ _ ha
  | reject ha => exact residual_reject ns swap left right extra ch _ _ ha
  | sendTally => exact residual_sendTally ns swap left right extra ch _
  | receivePartial => exact residual_receivePartial ns swap left right extra ch _
/-- The retained rejected trustee is internally quiescent under arbitrary
parallel restructuring. Its private visible input is handled by restriction. -/
theorem residual_rejected_no_tau (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (rs : List (Recipe 3)) (q : Agent Empty) :
    ¬ Agent.Tau (residual ns swap left right extra ch (.rejected rs)) q :=
  Agent.tau_input_no_step _ _ q

theorem residual_done_no_tau (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (rs : List (Recipe 3)) (q : Agent Empty) :
    ¬ Agent.Tau (residual ns swap left right extra ch (.done rs)) q :=
  Agent.tau_nil_no_step q
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
