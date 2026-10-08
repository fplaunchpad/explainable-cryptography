import ExplainableCrypto.Helios.Computational.BitOracleTapeCosted

/-! Observe complete source callers at a common actual tape-loop clock.
The observation decoder is proof-side interpretation, not a runtime instruction. -/
namespace ExplainableCrypto.Helios.Computational.BitOracleTapeLoop
open Turing OracleComp OracleSpec TM2TapeRuns BitOraclePortTransfer OracleTapeOutput
open BitOracleTapeCap
open BitOracleLoopBounded (Allowed Within adapter)

private def callerColumn {s : Nat} (i : Fin s) :
    PointedMap (TM2to1.Γ' (Ports s) (fun _ => Bool)) (Option Bool) :=
  ⟨fun cell => cell.2 (.inl i), rfl⟩

/-- Interpret all original source words only at a ready boundary. Other phases
are observable as unfinished. This does not add a free decoder to the machine. -/
def observeCaller {s l m : Nat} : State s l m → Option (BitOracleMachine.Config s l m)
  | .ready label memory tapes => some ⟨label, memory, fun i =>
      (OracleTapeDispatch.readWord (tapes.work.map (callerColumn i))).reverse⟩
  | _ => none

private theorem mapped_column {s l m : Nat} (cfg : BitOracleMachine.Config s l m) (i : Fin s) :
    (pack (BitOracleTapeCompute.framed cfg)).Tape.map (callerColumn i) =
      wordTape (cfg.stk i).reverse := by
  have col : (TM2to1.addBottom (columns (BitOracleTapeCompute.framed cfg).stk)).map (callerColumn i) =
      ListBlank.mk ((cfg.stk i).reverse.map some) := by
    apply ListBlank.ext
    intro n
    rw [ListBlank.nth_map]
    change ((TM2to1.addBottom (columns (BitOracleTapeCompute.framed cfg).stk)).nth n).2 (.inl i) = _
    rw [TM2to1.addBottom_nth_snd, columns_nth]
    change (cfg.stk i).reverse[n]? = _
    simp only [ListBlank.nth_mk, List.getI_eq_getElem?_getD, List.getElem?_map]
    cases (cfg.stk i).reverse[n]? <;> rfl
  simp only [pack, Tape.map_mk', wordTape, col]
  rfl

/-- Every canonical successor decodes to the complete original caller. -/
theorem observe_ready {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (query answer : Tape (Option Bool)) : observeCaller (ready cfg query answer) = some cfg := by
  have words : (fun i => (OracleTapeDispatch.readWord
      ((pack (BitOracleTapeCompute.framed cfg)).Tape.map (callerColumn i))).reverse) = cfg.stk := by
    funext i
    rw [mapped_column, OracleTapeDispatch.read_wordTape, List.reverse_reverse]
  simp only [observeCaller, ready, words]

private theorem run_halted {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (fuel : Nat) (cfg : BitOracleMachine.Config s l m) (query answer : Tape (Option Bool))
    (h : cfg.l = none) : run code fuel (ready cfg query answer) = pure (ready cfg query answer) := by
  have hs : step code (ready cfg query answer) = pure (ready cfg query answer) := by
    simp only [ready, step, h]
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [run, hs, pure_bind, ih]

private theorem simulate_node {α : Type} {M : Type → Type} [Monad M]
    (handler : QueryImpl BitOracleMachine.spec M) (q : BitOracleMachine.Request)
    (next : BitOracleMachine.spec.Range q → OracleComp BitOracleMachine.spec α) :
    simulateQ handler (OracleComp.queryBind q next) =
      (handler q >>= fun a => simulateQ handler (next a)) := rfl

/-- A costed tree and actual source halt justify padding at one observation
clock. Every allowed query/answer branch retains the complete caller result. -/
theorem costed_run {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (oa : OracleComp BitOracleMachine.spec (BitOracleMachine.Config s l m × Nat))
    (cap limit bound spent : Nat) (cfg : State s l m)
    (h : Costed code cap limit oa spent cfg) (hw : Within limit bound oa) :
    observeCaller <$> simulateQ (adapter limit) (run code (unitCost cap * bound - spent) cfg) =
      (fun out => some out.1) <$> simulateQ (adapter limit) oa := by
  induction oa generalizing spent cfg with
  | pure out =>
    obtain ⟨used, previous, answer, hu, he⟩ := h
    obtain ⟨hh, hb⟩ := hw
    have bound_cost := Nat.mul_le_mul_left (unitCost cap) hb
    have hn : unitCost cap * bound - spent = used + (unitCost cap * bound - spent - used) := by omega
    rw [hn, run_add, he, pure_bind, run_halted code _ _ _ _ hh]
    simp only [simulateQ_pure, map_pure, observe_ready]
    rfl
  | queryBind q next ih =>
    obtain ⟨before, continuation, he, hr⟩ := h
    have existsAnswer : ∃ a, Allowed limit q a := by
      cases q with
      | coin => exact ⟨false, trivial⟩
      | hash word => exact ⟨[], Nat.zero_le _⟩
    obtain ⟨answer, ha⟩ := existsAnswer
    have hb := costed_spent_le code (next answer) cap limit bound (spent + before)
      (continuation answer) (hr answer ha) (hw answer ha)
    have hn : unitCost cap * bound - spent = before + (unitCost cap * bound - (spent + before)) := by omega
    rw [hn, run_add, he]
    simp only [simulateQ_bind, simulate_node, simulateQ_pure, adapter,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    apply bind_congr
    intro a
    have hi := ih a.val (spent + before) (continuation a.val)
      (hr a.val a.property) (hw a.val a.property)
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using hi

/-- The original source charge/termination contract supplies one polynomial
tape clock. Initial height and previous-query size determine the global cap;
execution, presentation and accumulated tape work are all derived. -/
theorem run_source_bounded {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (sourceFuel limit bound : Nat) (cfg : BitOracleMachine.Config s l m)
    (previous : List Bool) (oldAnswer : Tape (Option Bool))
    (hw : Within limit bound (BitOracleMachine.run code sourceFuel cfg)) :
    let cap := height cfg.stk + bound + previous.length
    observeCaller <$> simulateQ (adapter limit)
      (run code (unitCost cap * bound) (ready cfg (wordTape previous) oldAnswer)) =
      (fun out => some out.1) <$> simulateQ (adapter limit) (BitOracleMachine.run code sourceFuel cfg) := by
  dsimp only
  have h := run_costed code sourceFuel cfg previous oldAnswer limit bound
    (height cfg.stk + bound + previous.length) hw (by omega) (by omega)
  simpa only [Nat.sub_zero] using costed_run code _
    (height cfg.stk + bound + previous.length) limit bound 0 _ h hw

/-- Common-clock equality transports through every lawful bounded-oracle
handler, including probabilistic stateful handlers and their complete effects. -/
theorem run_source_handler {s l m : Nat} {M : Type → Type} [Monad M] [LawfulMonad M]
    (code : BitOracleMachine.Code s l m) (sourceFuel limit bound : Nat)
    (cfg : BitOracleMachine.Config s l m) (previous : List Bool) (oldAnswer : Tape (Option Bool))
    (hw : Within limit bound (BitOracleMachine.run code sourceFuel cfg))
    (handler : QueryImpl (BitOracleLoopBounded.spec limit) M) :
    let cap := height cfg.stk + bound + previous.length
    observeCaller <$> simulateQ handler (simulateQ (adapter limit)
      (run code (unitCost cap * bound) (ready cfg (wordTape previous) oldAnswer))) =
      (fun out => some out.1) <$>
        simulateQ handler (simulateQ (adapter limit) (BitOracleMachine.run code sourceFuel cfg)) := by
  simpa only [simulateQ_map] using congrArg (simulateQ handler)
    (run_source_bounded code sourceFuel limit bound cfg previous oldAnswer hw)

end ExplainableCrypto.Helios.Computational.BitOracleTapeLoop
