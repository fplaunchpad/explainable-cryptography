import ExplainableCrypto.Helios.Symbolic.SourceClassifiedCommunication

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

theorem board_first_communication_classified (V : Type) (n extra : Nat) (ch : Channels)
    (key incoming : Ground) :
    Extended.InternalStep .communication
      (.plain (Extended.groundAgent (.par (.output (ch.voter 0) incoming .nil)
        (boardStart n extra ch key)) : Agent V))
      (.plain (Extended.groundAgent
        (.par .nil (.output ch.broadcast incoming (boardSecond n extra ch key incoming))))) := by
  have h := Extended.InternalStep.ground_message_communication V (ch.voter 0) incoming .nil
    (.output ch.broadcast (.var none) (boardSecond n extra ch (shiftTerm key) (.var none)))
  simpa only [boardStart,boardFirst_bind] using h

theorem residual_receiveFirst_classified (V : Type) (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) :
    Extended.InternalStep .communication
      (.plain (Extended.groundAgent (residual ns swap left right extra ch .start) : Agent V))
      (.plain (Extended.groundAgent (residual ns swap left right extra ch .firstReceived))) := by
  have h := (board_first_communication_classified V n extra ch (publicKey ns)
    (ballot ns 0 (choice swap left right 0).value)).plain_parLeft
      (Extended.groundAgent (.par (.output (ch.voter 1) (ballot ns 1 (choice swap left right 1).value) .nil)
        (trusteeAgent (n := n) ch (.name ns.secretKey))))
  let first := ballot ns 0 (choice swap left right 0).value
  let rest : Agent Empty := .par (.output (ch.voter 1) (ballot ns 1 (choice swap left right 1).value) .nil)
    (trusteeAgent (n := n) ch (.name ns.secretKey))
  refine Extended.InternalStep.ground_congr
    (p' := .par (.par (.output (ch.voter 0) first .nil) (boardStart n extra ch (publicKey ns))) rest)
    (q' := .par (.par .nil (.output ch.broadcast first (boardSecond n extra ch (publicKey ns) first))) rest)
    ?_ h ?_
  all_goals
    apply (Agent.parEq_iff_threads _ _).mpr
    simp only [first,rest,residual,electionBody,Agent.threads_par,Agent.threads_nil,zero_add,
      add_assoc,add_comm,add_left_comm]

theorem named_receiveFirst_classified (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) :
    Named.InternalStep .communication
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch .start))
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch .firstReceived)) :=
  .of_ground_communication _ _ _ rfl (residual_receiveFirst_classified _ ns swap left right extra ch)

theorem residual_sendTally_classified (V : Type) (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (rs : List (Recipe 3)) :
    Extended.InternalStep .communication
      (.plain (Extended.groundAgent (residual ns swap left right extra ch (.sendTally rs)) : Agent V))
      (.plain (Extended.groundAgent (residual ns swap left right extra ch (.trusteeReply rs)))) :=
  Extended.InternalStep.ground_message_communication V ch.trustee (sourceTallies ns swap left right rs)
    (.input ch.trustee (publishBody (n := n) ch (sourceTallies ns swap left right rs)))
    (.output ch.trustee (trusteeBody (n := n) (.name ns.secretKey)) .nil)

theorem named_sendTally_classified (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (rs : List (Recipe 3)) :
    Named.InternalStep .communication
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch (.sendTally rs)))
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch (.trusteeReply rs))) :=
  .of_ground_communication _ _ _ rfl (residual_sendTally_classified _ ns swap left right extra ch rs)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
