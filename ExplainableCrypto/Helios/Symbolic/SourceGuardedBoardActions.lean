import ExplainableCrypto.Helios.Symbolic.SourceGuardedBoard

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V : Type}

/-- The input has happened; acceptance still precedes the extended tally block. -/
def guardedBoardCheck (n remaining : Nat) (ch : Channels)
    (key first second : Term V) (others : List (Term V)) (incoming : Term V) : GuardedProgram V :=
  .branch (electionGuard n key (first :: second :: others) incoming)
    (guardedCollectBallots n ch remaining key first second (others ++ [incoming])) (.plain .nil)

theorem guardedCollectBallots_bind (n remaining : Nat) (ch : Channels)
    (key first second incoming : Term V) (others : List (Term V)) :
    (GuardedProgram.branch
      (electionGuard n (shiftTerm key)
        (shiftTerm first :: shiftTerm second :: others.map shiftTerm) (.var none))
      (guardedCollectBallots n ch remaining (shiftTerm key) (shiftTerm first) (shiftTerm second)
        (others.map shiftTerm ++ [.var none])) (.plain .nil)).subst (inputSubst incoming) =
      guardedBoardCheck n remaining ch key first second others incoming := by
  simp only [guardedBoardCheck,GuardedProgram.subst,electionGuard_subst,
    guardedCollectBallots_subst,shiftTerm_bind,List.map_cons,List.map_map,List.map_append,
    List.map_nil,Term.subst,inputSubst,Function.comp_def,List.map_id',Agent.subst]

theorem guardedCollectBallots_receives (n remaining : Nat) (ch : Channels)
    (key first second incoming : Term V) (others : List (Term V)) :
    Extended.FreeStep (guardedCollectBallots n ch (remaining+1) key first second others).expand
      (.input (ch.voter (others.length+2)) incoming)
      (guardedBoardCheck n remaining ch key first second others incoming).expand := by
  unfold guardedCollectBallots
  have h := GuardedProgram.receives (ch.voter (others.length+2)) incoming
    (GuardedProgram.branch
      (electionGuard n (shiftTerm key)
        (shiftTerm first :: shiftTerm second :: others.map shiftTerm) (.var none))
      (guardedCollectBallots n ch remaining (shiftTerm key) (shiftTerm first) (shiftTerm second)
        (others.map shiftTerm ++ [.var none])) (.plain .nil))
  rwa [guardedCollectBallots_bind] at h

theorem guardedBoardCheck_accepts (n remaining : Nat) (ch : Channels)
    (key first second incoming : Ground) (others : List Ground)
    (hf : (electionGuard n key (first :: second :: others) incoming).Holds Empty.elim) :
    Extended.Reduction (guardedBoardCheck n remaining ch key first second others incoming).expand
      (guardedCollectBallots n ch remaining key first second (others ++ [incoming])).expand :=
  GuardedProgram.selects_then _ _ _ hf

theorem guardedBoardCheck_rejects (n remaining : Nat) (ch : Channels)
    (key first second incoming : Ground) (others : List Ground)
    (hf : ¬ (electionGuard n key (first :: second :: others) incoming).Holds Empty.elim) :
    Extended.Reduction (guardedBoardCheck n remaining ch key first second others incoming).expand
      (.plain .nil) := GuardedProgram.selects_else _ _ _ hf

/-- The last acceptance activates every candidate let in the actual source AST. -/
theorem guardedBoardCheck_last_accepts (n : Nat) (ch : Channels)
    (key first second incoming : Ground) (others : List Ground)
    (hf : (electionGuard n key (first :: second :: others) incoming).Holds Empty.elim) :
    Extended.Reduction (guardedBoardCheck n 0 ch key first second others incoming).expand
      (boardTallyProgram (n := n) ch first second (others ++ [incoming])).compile := by
  have h := guardedBoardCheck_accepts n 0 ch key first second incoming others hf
  simpa only [guardedCollectBallots,GuardedProgram.ofProgram_expand] using h

theorem guardedBoardCheck_last_canonical (n : Nat) (ch : Channels)
    (key first second incoming : Ground) (others : List Ground)
    (hf : (electionGuard n key (first :: second :: others) incoming).Holds Empty.elim) :
    Extended.Reduction (guardedBoardCheck n 0 ch key first second others incoming).expand
      (.plain (boardFinish (n := n) ch first second (others ++ [incoming]))) :=
  .congr (.refl _) (guardedBoardCheck_last_accepts n ch key first second incoming others hf)
    (boardTallyProgram_normalizes ch first second (others ++ [incoming]))

theorem guardedBoardFirst_bind (n extra : Nat) (ch : Channels) (key incoming : Term V) :
    (GuardedProgram.output ch.broadcast (.var none)
      (guardedBoardSecond n extra ch (shiftTerm key) (.var none))).subst (inputSubst incoming) =
      .output ch.broadcast incoming (guardedBoardSecond n extra ch key incoming) := by
  simp only [GuardedProgram.subst,guardedBoardSecond_subst,shiftTerm_bind,Term.subst,inputSubst]

theorem guardedBoardSecond_bind (n extra : Nat) (ch : Channels) (key first incoming : Term V) :
    (GuardedProgram.output ch.broadcast (.var none)
      (guardedCollectBallots n ch extra (shiftTerm key) (shiftTerm first) (.var none) [])).subst
        (inputSubst incoming) =
      .output ch.broadcast incoming (guardedCollectBallots n ch extra key first incoming []) := by
  simp only [GuardedProgram.subst,guardedCollectBallots_subst,shiftTerm_bind,
    Term.subst,inputSubst,List.map_nil]

theorem guardedBoardFirst_receives (n extra : Nat) (ch : Channels) (key incoming : Term V) :
    Extended.FreeStep (guardedBoardStart n extra ch key).expand (.input (ch.voter 0) incoming)
      (GuardedProgram.output ch.broadcast incoming (guardedBoardSecond n extra ch key incoming)).expand := by
  have h := GuardedProgram.receives (ch.voter 0) incoming
    (GuardedProgram.output ch.broadcast (.var none)
      (guardedBoardSecond n extra ch (shiftTerm key) (.var none)))
  rwa [guardedBoardFirst_bind] at h

theorem guardedBoardSecond_receives (n extra : Nat) (ch : Channels) (key first incoming : Term V) :
    Extended.FreeStep (guardedBoardSecond n extra ch key first).expand (.input (ch.voter 1) incoming)
      (GuardedProgram.output ch.broadcast incoming
        (guardedCollectBallots n ch extra key first incoming [])).expand := by
  have h := GuardedProgram.receives (ch.voter 1) incoming
    (GuardedProgram.output ch.broadcast (.var none)
      (guardedCollectBallots n ch extra (shiftTerm key) (shiftTerm first) (.var none) []))
  rwa [guardedBoardSecond_bind] at h

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
