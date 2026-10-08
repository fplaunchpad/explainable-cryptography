import ExplainableCrypto.Helios.Symbolic.SourceElectionSyntax

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V W : Type} {n : Nat}

theorem shiftTerm_subst (t : Term V) (σ : V → Term W) :
    (shiftTerm t).subst (liftSubst σ) = shiftTerm (t.subst σ) := by
  simp only [shiftTerm,Term.subst_subst,Term.subst,liftSubst]

theorem shiftTerm_bind (t m : Term V) :
    (shiftTerm t).subst (inputSubst m) = t := by
  simp only [shiftTerm,Term.subst_subst,Term.subst,inputSubst,Term.subst_var]

theorem resultBody_subst (t : Term V) (σ : V → Term W) :
    (resultBody (n := n) t).subst (liftSubst σ) = resultBody (n := n) (t.subst σ) := by
  simp only [resultBody,candidateTuple_subst,Term.subst,Term.subst_project,liftSubst,
    Term.subst_subst]

theorem trusteeBody_subst (t : Term V) (σ : V → Term W) :
    (trusteeBody (n := n) t).subst (liftSubst σ) = trusteeBody (n := n) (t.subst σ) := by
  simp only [trusteeBody,candidateTuple_subst,Term.subst,Term.subst_project,liftSubst,
    Term.subst_subst]

theorem publishBody_subst (ch : Channels) (t : Term V) (σ : V → Term W) :
    (publishBody (n := n) ch t).subst (liftSubst σ) = publishBody (n := n) ch (t.subst σ) := by
  simp only [publishBody,Agent.subst,Term.subst,liftSubst,resultBody_subst]

theorem boardFinish_subst (ch : Channels) (first second : Term V) (others : List (Term V))
    (σ : V → Term W) :
    (boardFinish (n := n) ch first second others).subst σ =
      boardFinish (n := n) ch (first.subst σ) (second.subst σ) (others.map (Term.subst σ)) := by
  simp only [boardFinish,Agent.subst,publishBody_subst,tallyMessage_subst]

/-- The recursively generated board commutes with every variable substitution,
including substitutions whose messages themselves contain free variables. -/
theorem collectBallots_subst (n remaining : Nat) (ch : Channels)
    (key first second : Term V) (others : List (Term V)) (σ : V → Term W) :
    (collectBallots n ch remaining key first second others).subst σ =
      collectBallots n ch remaining (key.subst σ) (first.subst σ) (second.subst σ)
        (others.map (Term.subst σ)) := by
  induction remaining generalizing V W with
  | zero => exact boardFinish_subst ch first second others σ
  | succ remaining ih =>
    simp only [collectBallots,Agent.subst,electionGuard_subst,ih,shiftTerm_subst,
      List.map_cons,List.map_map,List.map_append,List.map_nil,List.length_map,
      Term.subst,liftSubst,Function.comp_def]

theorem boardSecond_subst (n extra : Nat) (ch : Channels) (key first : Term V) (σ : V → Term W) :
    (boardSecond n extra ch key first).subst σ =
      boardSecond n extra ch (key.subst σ) (first.subst σ) := by
  simp only [boardSecond,Agent.subst,collectBallots_subst,shiftTerm_subst,List.map_nil,Term.subst,liftSubst]

theorem boardStart_subst (n extra : Nat) (ch : Channels) (key : Term V) (σ : V → Term W) :
    (boardStart n extra ch key).subst σ = boardStart n extra ch (key.subst σ) := by
  simp only [boardStart,Agent.subst,boardSecond_subst,shiftTerm_subst,Term.subst,liftSubst]

theorem trusteeAgent_subst (ch : Channels) (secret : Term V) (σ : V → Term W) :
    (trusteeAgent (n := n) ch secret).subst σ = trusteeAgent (n := n) ch (secret.subst σ) := by
  simp only [trusteeAgent,Agent.subst,trusteeBody_subst]

/-- The complete next-input body after receiving one ballot. The previous
board is used for the check, and the new ballot is appended only in Then. -/
theorem collectBallots_bind (n remaining : Nat) (ch : Channels)
    (key first second incoming : Term V) (others : List (Term V)) :
    (Agent.branch
      (electionGuard n (shiftTerm key)
        (shiftTerm first :: shiftTerm second :: others.map shiftTerm) (.var none))
      (collectBallots n ch remaining (shiftTerm key) (shiftTerm first) (shiftTerm second)
        (others.map shiftTerm ++ [.var none])) .nil).bind incoming =
      .branch (electionGuard n key (first :: second :: others) incoming)
        (collectBallots n ch remaining key first second (others ++ [incoming])) .nil := by
  simp only [Agent.bind,Agent.subst,electionGuard_subst,collectBallots_subst,shiftTerm_bind,
    List.map_cons,List.map_map,List.map_append,List.map_nil,Term.subst,inputSubst,
    Function.comp_def,List.map_id']

theorem boardFirst_bind (n extra : Nat) (ch : Channels) (key incoming : Term V) :
    (Agent.output ch.broadcast (.var none)
      (boardSecond n extra ch (shiftTerm key) (.var none))).bind incoming =
      .output ch.broadcast incoming (boardSecond n extra ch key incoming) := by
  simp only [Agent.bind,Agent.subst,boardSecond_subst,shiftTerm_bind,Term.subst,inputSubst]

theorem boardSecond_bind (n extra : Nat) (ch : Channels) (key first incoming : Term V) :
    (Agent.output ch.broadcast (.var none)
      (collectBallots n ch extra (shiftTerm key) (shiftTerm first) (.var none) [])).bind incoming =
      .output ch.broadcast incoming (collectBallots n ch extra key first incoming []) := by
  simp only [Agent.bind,Agent.subst,collectBallots_subst,shiftTerm_bind,Term.subst,inputSubst,List.map_nil]

theorem publishBody_bind (ch : Channels) (tallies partials : Term V) :
    (publishBody (n := n) ch tallies).bind partials =
      .output ch.broadcast partials
        (.output ch.broadcast (resultMessage (n := n) tallies partials) .nil) := rfl
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
