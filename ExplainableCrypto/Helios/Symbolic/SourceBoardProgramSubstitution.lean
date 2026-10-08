import ExplainableCrypto.Helios.Symbolic.SourceGuardedProgram
import ExplainableCrypto.Helios.Symbolic.SourceBoardTallyBridge

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V W U : Type} {n : Nat}

namespace BoardTallyRegisters

theorem map_comp (s : BoardTallyRegisters n V) (σ : V → Term W) (τ : W → Term U) :
    (s.map σ).map τ = s.map (fun v => (σ v).subst τ) := by
  cases s
  simp only [map,Term.subst_subst]

theorem shift_map (s : BoardTallyRegisters n V) (σ : V → Term W) :
    s.shift.map (liftSubst σ) = (s.map σ).shift := by
  simp only [shift,map_comp,Term.subst,liftSubst]

theorem afterBind_subst (s : BoardTallyRegisters n V) (j : Fin (n+1)) (σ : V → Term W) :
    (s.afterBind j).map (liftSubst σ) = (s.map σ).afterBind j := by
  classical
  cases s
  dsimp only [afterBind,map,shift]
  congr 1 <;> funext k <;> by_cases hk : k=j
  all_goals simp_all [Term.subst,Term.subst_subst,liftSubst]

end BoardTallyRegisters

theorem boardTallyComponents_subst (ch : Channels) (indices : List (Fin (n+1)))
    (s : BoardTallyRegisters n V) (σ : V → Term W) :
    (boardTallyComponents ch indices s).subst σ = boardTallyComponents ch indices (s.map σ) := by
  induction indices generalizing V W with
  | nil => simp only [boardTallyComponents,AgentProgram.subst,boardRegisterFinish_subst,
      candidateTuple_subst,BoardTallyRegisters.map]
  | cons j js ih =>
    simp only [boardTallyComponents,AgentProgram.subst,ih,BoardTallyRegisters.afterBind_subst]
    rfl

theorem boardTallyProgram_subst (ch : Channels) (first second : Term V)
    (others : List (Term V)) (σ : V → Term W) :
    (boardTallyProgram (n := n) ch first second others).subst σ =
      boardTallyProgram (n := n) ch (first.subst σ) (second.subst σ) (others.map (Term.subst σ)) := by
  simp only [boardTallyProgram,boardTallyComponents_subst,boardTallyInitial,
    BoardTallyRegisters.map,boardTally_subst,Term.subst]

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
