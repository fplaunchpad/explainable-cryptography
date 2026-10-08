import ExplainableCrypto.Helios.Symbolic.SourceElectionBinding

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- The first authenticated input retains its message for the public relay. -/
theorem board_first_communication (n extra : Nat) (ch : Channels) (key incoming : Ground) :
    Agent.CoreStep
      (.par (.output (ch.voter 0) incoming .nil) (boardStart n extra ch key))
      (.par .nil (.output ch.broadcast incoming (boardSecond n extra ch key incoming))) := by
  have h := Agent.CoreStep.comm (ch.voter 0) incoming .nil
    (.output ch.broadcast (.var none) (boardSecond n extra ch (shiftTerm key) (.var none)))
  simpa only [boardStart,boardFirst_bind] using h

theorem board_second_communication (n extra : Nat) (ch : Channels) (key first incoming : Ground) :
    Agent.CoreStep
      (.par (.output (ch.voter 1) incoming .nil) (boardSecond n extra ch key first))
      (.par .nil (.output ch.broadcast incoming (collectBallots n ch extra key first incoming []))) := by
  have h := Agent.CoreStep.comm (ch.voter 1) incoming .nil
    (.output ch.broadcast (.var none)
      (collectBallots n ch extra (shiftTerm key) (shiftTerm first) (.var none) []))
  simpa only [boardSecond,boardSecond_bind] using h

/-- Direct delivery leaves a pending check, without any attacker-ballot public
relay. Labelled input and its public-recipe restriction are separate rules. -/
theorem collection_communication (n remaining : Nat) (ch : Channels)
    (key first second incoming : Ground) (others : List Ground) :
    Agent.CoreStep
      (.par (.output (ch.voter (others.length+2)) incoming .nil)
        (collectBallots n ch (remaining+1) key first second others))
      (.par .nil (.branch (electionGuard n key (first :: second :: others) incoming)
        (collectBallots n ch remaining key first second (others ++ [incoming])) .nil)) := by
  rw [collectBallots]
  have h := Agent.CoreStep.comm (ch.voter (others.length+2)) incoming .nil
    (.branch (electionGuard n (shiftTerm key)
      (shiftTerm first :: shiftTerm second :: others.map shiftTerm) (.var none))
      (collectBallots n ch remaining (shiftTerm key) (shiftTerm first) (shiftTerm second)
        (others.map shiftTerm ++ [.var none])) .nil)
  simpa only [collectBallots_bind] using h

/-- Accepted appends the received ballot exactly once before continuing. -/
theorem collection_accept (n remaining : Nat) (ch : Channels)
    (key first second incoming : Ground) (others : List Ground)
    (ha : Accepted n key (first :: second :: others) incoming) :
    Agent.CoreStep
      (.branch (electionGuard n key (first :: second :: others) incoming)
        (collectBallots n ch remaining key first second (others ++ [incoming])) .nil)
      (collectBallots n ch remaining key first second (others ++ [incoming])) :=
  .thenBranch _ _ _ ((electionGuard_ground _ _ _ _).mpr ha)

/-- Rejection consumes no later voters and returns null. -/
theorem collection_reject (n remaining : Nat) (ch : Channels)
    (key first second incoming : Ground) (others : List Ground)
    (ha : ¬ Accepted n key (first :: second :: others) incoming) :
    Agent.CoreStep
      (.branch (electionGuard n key (first :: second :: others) incoming)
        (collectBallots n ch remaining key first second (others ++ [incoming])) .nil) .nil :=
  .elseBranch _ _ _ (fun h => ha ((electionGuard_ground _ _ _ _).mp h))

/-- Both directions of the stage acceptance predicate now have a literal
finite source guard interpreted in the public initial frame. -/
theorem evaluated_guard_accepts (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (r : Recipe 3) :
    (electionGuard n (.var 0) (honestBoardRecipes ++ rs) r).Holds (frame ns swap left right).value ↔
      Process.accepts ns swap left right rs r := by
  have hk : (Term.var (0 : Fin 3)).subst (frame ns swap left right).value = publicKey ns := rfl
  unfold Process.accepts Frame.eval
  simpa only [hk] using
    electionGuard_holds n (.var 0) (honestBoardRecipes ++ rs) r (frame ns swap left right).value

/-- The literal source check has the same truth in the two voting worlds,
by B7 and the checked public syntax of the finite formula. -/
theorem evaluated_guard_swap (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (r : Recipe 3)
    (hp : ∀ s ∈ rs, s.Public ns.restricted) (hr : r.Public ns.restricted) :
    (electionGuard n (.var 0) (honestBoardRecipes ++ rs) r).Holds (frame ns false left right).value ↔
    (electionGuard n (.var 0) (honestBoardRecipes ++ rs) r).Holds (frame ns true left right).value := by
  apply Formula.holds_staticEq (initial_frame_staticEq ns hf left right)
  apply electionGuard_public n (.var 0) (honestBoardRecipes ++ rs) r ns.restricted trivial hr
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · simp only [honestBoardRecipes,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl <;> trivial
  · exact hp s hs

/-- The board and trustee exchange the complete tally tuple. -/
theorem board_tally_communication (ch : Channels) (first second secret : Ground) (others : List Ground) :
    let tallies := tallyMessage (n := n) first second others
    Agent.CoreStep
      (.par (boardFinish (n := n) ch first second others) (trusteeAgent (n := n) ch secret))
      (.par (.input ch.trustee (publishBody (n := n) ch tallies))
        (.output ch.trustee (trusteeMessage (n := n) secret tallies) .nil)) := by
  exact .comm _ _ _ _

/-- Reply substitution preserves the two public outputs and their source order.
The reversed parallel layout is explicit; structural commutation is not assumed. -/
theorem board_reply_communication (ch : Channels) (tallies partials : Ground) :
    Agent.CoreStep
      (.par (.output ch.trustee partials .nil) (.input ch.trustee (publishBody (n := n) ch tallies)))
      (.par .nil (.output ch.broadcast partials
        (.output ch.broadcast (resultMessage (n := n) tallies partials) .nil))) :=
  .comm _ _ _ _
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
