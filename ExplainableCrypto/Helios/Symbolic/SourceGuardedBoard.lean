import ExplainableCrypto.Helios.Symbolic.SourceBoardProgramSubstitution
import ExplainableCrypto.Helios.Symbolic.SourceGuardedActivation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V W : Type} {n : Nat}

/-- Figure 4's complete public collection chain, retaining the final explicit
tally lets beneath every input and acceptance guard. -/
def guardedCollectBallots (n : Nat) (ch : Channels) :
    Nat → {V : Type} → Term V → Term V → Term V → List (Term V) → GuardedProgram V
  | 0, _, _, first, second, others =>
      .ofProgram (boardTallyProgram (n := n) ch first second others)
  | remaining+1, _, key, first, second, others =>
      .input (ch.voter (others.length+2))
        (.branch
          (electionGuard n (shiftTerm key)
            (shiftTerm first :: shiftTerm second :: others.map shiftTerm) (.var none))
          (guardedCollectBallots n ch remaining (shiftTerm key) (shiftTerm first) (shiftTerm second)
            (others.map shiftTerm ++ [.var none]))
          (.plain .nil))

def guardedBoardSecond (n extra : Nat) (ch : Channels) (key first : Term V) : GuardedProgram V :=
  .input (ch.voter 1) (.output ch.broadcast (.var none)
    (guardedCollectBallots n ch extra (shiftTerm key) (shiftTerm first) (.var none) []))

def guardedBoardStart (n extra : Nat) (ch : Channels) (key : Term V) : GuardedProgram V :=
  .input (ch.voter 0) (.output ch.broadcast (.var none)
    (guardedBoardSecond n extra ch (shiftTerm key) (.var none)))

theorem guardedCollectBallots_subst (n remaining : Nat) (ch : Channels)
    (key first second : Term V) (others : List (Term V)) (σ : V → Term W) :
    (guardedCollectBallots n ch remaining key first second others).subst σ =
      guardedCollectBallots n ch remaining (key.subst σ) (first.subst σ) (second.subst σ)
        (others.map (Term.subst σ)) := by
  induction remaining generalizing V W with
  | zero => simp only [guardedCollectBallots,GuardedProgram.ofProgram_subst,boardTallyProgram_subst]
  | succ remaining ih =>
    simp only [guardedCollectBallots,GuardedProgram.subst,electionGuard_subst,ih,shiftTerm_subst,
      List.map_cons,List.map_map,List.map_append,List.map_nil,List.length_map,
      Term.subst,liftSubst,Function.comp_def,Agent.subst]

theorem guardedBoardSecond_subst (n extra : Nat) (ch : Channels) (key first : Term V) (σ : V → Term W) :
    (guardedBoardSecond n extra ch key first).subst σ =
      guardedBoardSecond n extra ch (key.subst σ) (first.subst σ) := by
  simp only [guardedBoardSecond,GuardedProgram.subst,guardedCollectBallots_subst,shiftTerm_subst,
    List.map_nil,Term.subst,liftSubst]

theorem guardedBoardStart_subst (n extra : Nat) (ch : Channels) (key : Term V) (σ : V → Term W) :
    (guardedBoardStart n extra ch key).subst σ = guardedBoardStart n extra ch (key.subst σ) := by
  simp only [guardedBoardStart,GuardedProgram.subst,guardedBoardSecond_subst,
    shiftTerm_subst,Term.subst,liftSubst]

theorem boardTallyProgram_inline_equivE (ch : Channels) (first second : Term V)
    (others : List (Term V)) :
    Agent.EquivE (GuardedProgram.ofProgram (boardTallyProgram (n := n) ch first second others)).inline
      (boardFinish (n := n) ch first second others) := by
  rw [GuardedProgram.ofProgram_inline,boardTallyProgram_value]
  apply Agent.EquivE.output _ (.refl _)
  apply Agent.EquivE.input
  apply Agent.EquivE.output _ (.refl _)
  apply Agent.EquivE.output _ ?_ .nil
  apply EqE.candidateTuple
  intro j
  apply EqE.binary .dec (.refl _)
  simpa only [shiftTerm,tallyMessage,Term.subst_project] using
    ((candidateTuple_project (boardTally first second others) j).symm.subst
      (fun v => Term.var (some v)))

/-- Full-E congruence of the compiled plain board, not a new Structural rule. -/
theorem guardedCollectBallots_inline_equivE (n remaining : Nat) (ch : Channels)
    (key first second : Term V) (others : List (Term V)) :
    Agent.EquivE (guardedCollectBallots n ch remaining key first second others).inline
      (collectBallots n ch remaining key first second others) := by
  induction remaining generalizing V with
  | zero => exact boardTallyProgram_inline_equivE ch first second others
  | succ remaining ih =>
    exact .input _ (.branch (.refl _) (ih _ _ _ _) .nil)

theorem guardedBoardSecond_inline_equivE (n extra : Nat) (ch : Channels) (key first : Term V) :
    Agent.EquivE (guardedBoardSecond n extra ch key first).inline (boardSecond n extra ch key first) :=
  .input _ (.output _ (.refl _) (guardedCollectBallots_inline_equivE n extra ch _ _ _ _))

theorem guardedBoardStart_inline_equivE (n extra : Nat) (ch : Channels) (key : Term V) :
    Agent.EquivE (guardedBoardStart n extra ch key).inline (boardStart n extra ch key) :=
  .input _ (.output _ (.refl _) (guardedBoardSecond_inline_equivE n extra ch _ _))

/-- At the reached tally block, correspondence uses the actual source relation. -/
theorem guardedCollectBallots_zero_normalizes (n : Nat) (ch : Channels)
    (key first second : Term V) (others : List (Term V)) :
    Extended.Structural (guardedCollectBallots n ch 0 key first second others).expand
      (.plain (boardFinish (n := n) ch first second others)) := by
  rw [guardedCollectBallots,GuardedProgram.ofProgram_expand]
  exact boardTallyProgram_normalizes ch first second others

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
