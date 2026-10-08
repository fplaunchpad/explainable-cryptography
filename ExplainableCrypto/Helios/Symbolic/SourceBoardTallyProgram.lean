import ExplainableCrypto.Helios.Symbolic.SourceFiniteSubstitution

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V W : Type} {n : Nat}

/-- Figure 4's direct tally-register continuation. The newly received partial
is None, and every saved tally is shifted past that input. -/
def boardRegisterFinish (ch : Channels) (message : Term V) (tallies : Fin (n+1) → Term V) : Agent V :=
  .output ch.trustee message (.input ch.trustee
    (.output ch.broadcast (.var none)
      (.output ch.broadcast (candidateTuple (fun j => .binary .dec
        ((Term.var none).project j.val) (shiftTerm (tallies j)))) .nil)))

theorem boardRegisterFinish_subst (ch : Channels) (message : Term V)
    (tallies : Fin (n+1) → Term V) (σ : V → Term W) :
    (boardRegisterFinish ch message tallies).subst σ =
      boardRegisterFinish ch (message.subst σ) (fun j => (tallies j).subst σ) := by
  simp only [boardRegisterFinish,Agent.subst,candidateTuple_subst,Term.subst,
    Term.subst_project,shiftTerm_subst,liftSubst]

/-- Fixed candidate expressions and initially empty saved tally registers. -/
structure BoardTallyRegisters (n : Nat) (V : Type) where
  expressions : Fin (n+1) → Term V
  tallies : Fin (n+1) → Term V

namespace BoardTallyRegisters

def map (s : BoardTallyRegisters n V) (σ : V → Term W) : BoardTallyRegisters n W :=
  ⟨fun j => (s.expressions j).subst σ,fun j => (s.tallies j).subst σ⟩

def shift (s : BoardTallyRegisters n V) : BoardTallyRegisters n (Option V) :=
  s.map (fun v => .var (some v))

def compute (s : BoardTallyRegisters n V) (j : Fin (n+1)) : BoardTallyRegisters n V :=
  { s with tallies := Function.update s.tallies j (s.expressions j) }

def afterBind (s : BoardTallyRegisters n V) (j : Fin (n+1)) : BoardTallyRegisters n (Option V) :=
  { s.shift with tallies := Function.update s.shift.tallies j (.var none) }

noncomputable def completed (s : BoardTallyRegisters n V) (indices : List (Fin (n+1))) : BoardTallyRegisters n V :=
  { s with tallies := fun j => if j ∈ indices then s.expressions j else s.tallies j }

theorem afterBind_map (s : BoardTallyRegisters n V) (j : Fin (n+1)) (σ : V → Term W) :
    (s.afterBind j).map (extendEnv σ ((s.expressions j).subst σ)) = (s.map σ).compute j := by
  classical
  cases s
  dsimp only [afterBind,map,shift,compute]
  congr 1 <;> funext k <;> by_cases hk : k=j
  all_goals simp_all [Term.subst,Term.subst_subst,extendEnv]

theorem completed_compute (s : BoardTallyRegisters n V) (j : Fin (n+1)) (indices : List (Fin (n+1))) :
    (s.compute j).completed indices = s.completed (j::indices) := by
  classical
  cases s
  dsimp only [compute,completed]
  congr 1
  funext k
  by_cases hk : k=j <;> by_cases hm : k ∈ indices <;> simp [hk,hm]

end BoardTallyRegisters

/-- Bind each candidate tally once, in the specified order, then send the full
tuple and use those same registers for the final decryptions. -/
def boardTallyComponents (ch : Channels) :
    List (Fin (n+1)) → {V : Type} → BoardTallyRegisters n V → AgentProgram V
  | [], _, s => .result (boardRegisterFinish ch (candidateTuple s.tallies) s.tallies)
  | j::js, _, s => .letTerm (s.expressions j) (boardTallyComponents ch js (s.afterBind j))

theorem boardTallyComponents_eval (ch : Channels) (indices : List (Fin (n+1)))
    (s : BoardTallyRegisters n V) (σ : V → Term W) :
    (boardTallyComponents ch indices s).eval σ =
      let t := ((s.map σ).completed indices).tallies
      boardRegisterFinish ch (candidateTuple t) t := by
  induction indices generalizing V W with
  | nil => simp only [boardTallyComponents,AgentProgram.eval,boardRegisterFinish_subst,
      candidateTuple_subst,BoardTallyRegisters.completed,List.not_mem_nil,ite_false,BoardTallyRegisters.map]
  | cons j js ih => simp only [boardTallyComponents,AgentProgram.eval,ih,
      BoardTallyRegisters.afterBind_map,BoardTallyRegisters.completed_compute]

theorem boardTallyComponents_bindings (ch : Channels) (indices : List (Fin (n+1)))
    (s : BoardTallyRegisters n V) : (boardTallyComponents ch indices s).bindings = indices.length := by
  induction indices generalizing V with
  | nil => rfl
  | cons j js ih => simp only [boardTallyComponents,AgentProgram.bindings,ih,List.length_cons,Nat.add_comm]

def boardTallyInitial (first second : Term V) (others : List (Term V)) : BoardTallyRegisters n V :=
  ⟨boardTally first second others,fun _ => .const .bottom⟩

def boardTallyProgram (ch : Channels) (first second : Term V) (others : List (Term V)) : AgentProgram V :=
  boardTallyComponents ch (List.finRange (n+1)) (boardTallyInitial first second others)

theorem boardTallyProgram_value (ch : Channels) (first second : Term V) (others : List (Term V)) :
    (boardTallyProgram (n := n) ch first second others).value =
      boardRegisterFinish (n := n) ch (tallyMessage (n := n) first second others) (boardTally first second others) := by
  have h := boardTallyComponents_eval ch (List.finRange (n+1))
    (boardTallyInitial (n := n) first second others) Term.var
  rw [AgentProgram.eval_var] at h
  simpa only [boardTallyProgram,boardTallyInitial,BoardTallyRegisters.map,Term.subst_var,
    BoardTallyRegisters.completed,List.mem_finRange,ite_true,tallyMessage] using h

theorem boardTallyProgram_bindings (ch : Channels) (first second : Term V) (others : List (Term V)) :
    (boardTallyProgram (n := n) ch first second others).bindings = n+1 := by
  simpa only [boardTallyProgram,List.length_finRange] using
    boardTallyComponents_bindings ch (List.finRange (n+1)) (boardTallyInitial first second others)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
