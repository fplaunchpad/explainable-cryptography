import ExplainableCrypto.Helios.Computational.NativeWordCompiler
import ExplainableCrypto.Helios.Computational.NativeAdaptiveProbe
import ExplainableCrypto.Helios.Computational.BitOracleReturnLink

/-! Exact generated local segments for the fixed adaptive source. The native
command is selected from all original heads before its generated action runs.
Each move below uses a nonblank bit established by the preceding write. -/
namespace ExplainableCrypto.Helios.Computational.NativeAdaptiveSegments
open Turing OracleComp OracleSpec
set_option maxRecDepth 32768
set_option maxHeartbeats 600000

def words (wb wr qb qr ab ar : List Bool) : Fin 6 → List Bool := ![wb,wr,qb,qr,ab,ar]

/-- Charges are computed from the generated syntax, including both branches of
its unsupported-action guard. -/
theorem entry_cost (l : Fin 9) :
    BitOracleMachine.localCost (NativeWordCompiler.entry l) = 4 := rfl

theorem write_cost (l : Fin 9) (b : Bool) :
    BitOracleMachine.localCost (NativeWordCompiler.localProgram l
      ![none,some (.write (some b)),none]) = 4 := rfl

theorem right_cost (l : Fin 9) :
    BitOracleMachine.localCost (NativeWordCompiler.localProgram l
      ![none,some (.move .right),none]) = 5 := rfl

theorem left_cost (l : Fin 9) :
    BitOracleMachine.localCost (NativeWordCompiler.localProgram l
      ![none,some (.move .left),none]) = 5 := rfl

private theorem heads_snapshot (ws : Fin 6 → List Bool) :
    NativeWordCompiler.heads (NativeWordCompiler.snapshot ws) =
      ![(ws 1).head?,(ws 3).head?,(ws 5).head?] := by
  unfold NativeWordCompiler.snapshot
  generalize h0 : (ws 1).head? = a
  generalize h1 : (ws 3).head? = b
  generalize h2 : (ws 5).head? = c
  funext i
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases i <;> rfl

private theorem local_pair (q next : Fin 9) (ws : Fin 6 → List Bool)
    (acts : Fin 3 → Option (TM0.Stmt (Option Bool)))
    (hc : NativeAdaptiveProbe.code q (NativeWordCompiler.heads (NativeWordCompiler.snapshot ws)) =
      .local next acts) :
    BitOracleMachine.run (NativeWordCompiler.code NativeAdaptiveProbe.code) 2
      (NativeWordCompiler.present (some q) ws) =
      pure (TM2.stepAux (NativeWordCompiler.localProgram next acts)
        (NativeWordCompiler.snapshot ws) ws,
        4+BitOracleMachine.localCost (NativeWordCompiler.localProgram next acts)) := by
  rw [BitOracleMachine.run,NativeWordCompiler.entry_step]
  simp only [pure_bind]
  have hs : BitOracleMachine.step (NativeWordCompiler.code NativeAdaptiveProbe.code)
      (⟨some (NativeWordCompiler.commandLabel q (NativeWordCompiler.snapshot ws)),
        NativeWordCompiler.snapshot ws,ws⟩ : NativeWordCompiler.Config 9) =
      pure (TM2.stepAux (NativeWordCompiler.localProgram next acts)
        (NativeWordCompiler.snapshot ws) ws,
        BitOracleMachine.localCost (NativeWordCompiler.localProgram next acts)) := by
    simp only [BitOracleMachine.step,NativeWordCompiler.code_command,NativeWordCompiler.command,hc]
  rw [BitOracleMachine.run,hs]
  simp only [pure_bind,BitOracleMachine.run,Nat.add_zero]

private theorem branch_write (wb wr input reply : List Bool) :
    BitOracleMachine.run (NativeWordCompiler.code NativeAdaptiveProbe.code) 2
      (NativeWordCompiler.present (some 1) (words wb wr [] input [] reply)) =
      pure (NativeWordCompiler.present (some (if reply.headD false then 2 else 3))
        (words wb wr [] (reply.headD false::input.tail) [] reply),8) := by
  let ws := words wb wr [] input [] reply
  let next : Fin 9 := if reply.headD false then 2 else 3
  let acts : Fin 3 → Option (TM0.Stmt (Option Bool)) :=
    ![none,some (.write (some (reply.headD false))),none]
  have hc : NativeAdaptiveProbe.code 1 (NativeWordCompiler.heads (NativeWordCompiler.snapshot ws)) =
      .local next acts := by
    rw [heads_snapshot]
    cases reply with
    | nil => rfl
    | cons b rest => cases b <;> rfl
  have hs : TM2.stepAux (NativeWordCompiler.localProgram next acts)
      (NativeWordCompiler.snapshot ws) ws =
      NativeWordCompiler.present (some next)
        (words wb wr [] (reply.headD false::input.tail) [] reply) := by
    apply congrArg (fun words : Fin 6 → List Bool =>
      (⟨some (NativeWordCompiler.entryLabel next),0,words⟩ : NativeWordCompiler.Config 9))
    funext k
    fin_cases k <;> rfl
  rw [local_pair 1 next ws acts hc,hs]
  rfl

private theorem right_move (wb wr before rest reply : List Bool) (b : Bool) :
    BitOracleMachine.run (NativeWordCompiler.code NativeAdaptiveProbe.code) 2
      (NativeWordCompiler.present (some (if b then 2 else 3))
        (words wb wr before (b::rest) [] reply)) =
      pure (NativeWordCompiler.present (some 4) (words wb wr (b::before) rest [] reply),9) := by
  let ws := words wb wr before (b::rest) [] reply
  let q : Fin 9 := if b then 2 else 3
  let acts : Fin 3 → Option (TM0.Stmt (Option Bool)) := ![none,some (.move .right),none]
  have hc : NativeAdaptiveProbe.code q (NativeWordCompiler.heads (NativeWordCompiler.snapshot ws)) =
      .local 4 acts := by cases b <;> rfl
  have hs : TM2.stepAux (NativeWordCompiler.localProgram (4 : Fin 9) acts) (NativeWordCompiler.snapshot ws) ws =
      NativeWordCompiler.present (some 4) (words wb wr (b::before) rest [] reply) := by
    cases b <;>
      apply congrArg (fun words : Fin 6 → List Bool =>
        (⟨some (NativeWordCompiler.entryLabel 4),0,words⟩ : NativeWordCompiler.Config 9)) <;>
      funext k <;> fin_cases k <;> rfl
  rw [local_pair q 4 ws acts hc,hs]
  rfl

/-- Both generated native-local transitions, including the answer-selected
branch and the supported right move, with their actual charge. -/
theorem branch_move (wb wr input reply : List Bool) :
    BitOracleMachine.run (NativeWordCompiler.code NativeAdaptiveProbe.code) 4
      (NativeWordCompiler.present (some 1) (words wb wr [] input [] reply)) =
      pure (NativeWordCompiler.present (some 4)
        (words wb wr [reply.headD false] input.tail [] reply),17) := by
  change BitOracleMachine.run _ (2+2) _ = _
  rw [BitOracleReturnLink.run_add,branch_write]
  simp only [pure_bind]
  rw [right_move]
  simp only [pure_bind]

private theorem coin_write (wb wr before rest : List Bool) (coin : Bool) :
    BitOracleMachine.run (NativeWordCompiler.code NativeAdaptiveProbe.code) 2
      (NativeWordCompiler.present (some 5) (words wb wr before rest [] [coin])) =
      pure (NativeWordCompiler.present (some 6)
        (words wb wr before (coin::rest.tail) [] [coin]),8) := by
  let ws := words wb wr before rest [] [coin]
  let acts : Fin 3 → Option (TM0.Stmt (Option Bool)) := ![none,some (.write (some coin)),none]
  have hc : NativeAdaptiveProbe.code 5 (NativeWordCompiler.heads (NativeWordCompiler.snapshot ws)) =
      .local 6 acts := by
    rw [heads_snapshot]
    cases coin <;> rfl
  have hs : TM2.stepAux (NativeWordCompiler.localProgram (6 : Fin 9) acts) (NativeWordCompiler.snapshot ws) ws =
      NativeWordCompiler.present (some 6) (words wb wr before (coin::rest.tail) [] [coin]) := by
    apply congrArg (fun words : Fin 6 → List Bool =>
      (⟨some (NativeWordCompiler.entryLabel 6),0,words⟩ : NativeWordCompiler.Config 9))
    funext k
    fin_cases k <;> rfl
  rw [local_pair 5 6 ws acts hc,hs]
  rfl

private theorem left_move (wb wr before rest reply : List Bool) (b : Bool) :
    BitOracleMachine.run (NativeWordCompiler.code NativeAdaptiveProbe.code) 2
      (NativeWordCompiler.present (some 6) (words wb wr (b::before) rest [] reply)) =
      pure (NativeWordCompiler.present (some 7) (words wb wr before (b::rest) [] reply),9) := by
  let ws := words wb wr (b::before) rest [] reply
  let acts : Fin 3 → Option (TM0.Stmt (Option Bool)) := ![none,some (.move .left),none]
  have hc : NativeAdaptiveProbe.code 6 (NativeWordCompiler.heads (NativeWordCompiler.snapshot ws)) =
      .local 7 acts := rfl
  have hs : TM2.stepAux (NativeWordCompiler.localProgram (7 : Fin 9) acts) (NativeWordCompiler.snapshot ws) ws =
      NativeWordCompiler.present (some 7) (words wb wr before (b::rest) [] reply) := by
    cases b <;>
      apply congrArg (fun words : Fin 6 → List Bool =>
        (⟨some (NativeWordCompiler.entryLabel 7),0,words⟩ : NativeWordCompiler.Config 9)) <;>
      funext k <;> fin_cases k <;> rfl
  rw [local_pair 6 7 ws acts hc,hs]
  rfl

/-- The actual received coin is written before returning the query head left. -/
theorem coin_write_left (wb wr rest : List Bool) (branch coin : Bool) :
    BitOracleMachine.run (NativeWordCompiler.code NativeAdaptiveProbe.code) 4
      (NativeWordCompiler.present (some 5) (words wb wr [branch] rest [] [coin])) =
      pure (NativeWordCompiler.present (some 7)
        (words wb wr [] (branch::coin::rest.tail) [] [coin]),17) := by
  change BitOracleMachine.run _ (2+2) _ = _
  rw [BitOracleReturnLink.run_add,coin_write]
  simp only [pure_bind]
  rw [left_move]
  simp only [pure_bind]

theorem halt_run (ws : Fin 6 → List Bool) :
    BitOracleMachine.run (NativeWordCompiler.code NativeAdaptiveProbe.code) 2
      (NativeWordCompiler.present (some 8) ws) =
      pure (NativeWordCompiler.present none ws,6) := by
  rw [BitOracleMachine.run,NativeWordCompiler.entry_step]
  simp only [pure_bind]
  have hs : BitOracleMachine.step (NativeWordCompiler.code NativeAdaptiveProbe.code)
      (⟨some (NativeWordCompiler.commandLabel 8 (NativeWordCompiler.snapshot ws)),
        NativeWordCompiler.snapshot ws,ws⟩ : NativeWordCompiler.Config 9) =
      pure (NativeWordCompiler.present none ws,2) := by
    simp only [BitOracleMachine.step,NativeWordCompiler.code_command,NativeWordCompiler.command]
    rfl
  rw [BitOracleMachine.run,hs]
  simp only [pure_bind,BitOracleMachine.run,Nat.add_zero]

end ExplainableCrypto.Helios.Computational.NativeAdaptiveSegments
