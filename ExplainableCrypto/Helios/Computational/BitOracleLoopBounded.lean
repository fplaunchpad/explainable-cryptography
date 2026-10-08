import ExplainableCrypto.Helios.Computational.BitOracleLoopCorrespondence

/-! Uniform observations of terminating raw programs under an explicit encoded
oracle-response contract. Requests are unchanged. The bounded interface is a
semantic adapter; the actual scalar handler must derive this output contract. -/
namespace ExplainableCrypto.Helios.Computational.BitOracleLoopBounded
open OracleComp OracleSpec Turing.TM2
open BitOracleLoop

/-- Coins retain both values; only native hash response word length is bounded. -/
def Allowed (limit : Nat) : (q : BitOracleMachine.Request) → BitOracleMachine.spec.Range q → Prop
  | .coin, _ => True
  | .hash _, answer => answer.length ≤ limit

/-- The interface accepts every raw request and returns a word satisfying the
encoded oracle's output-size contract. -/
def spec (limit : Nat) : OracleSpec BitOracleMachine.Request :=
  fun q => {answer : BitOracleMachine.spec.Range q // Allowed limit q answer}

private def defaultAnswer (limit : Nat) : (q : BitOracleMachine.Request) → (spec limit).Range q
  | .coin => ⟨false, trivial⟩
  | .hash _ => ⟨[], Nat.zero_le _⟩

/-- Erase the bounded oracle's proof without altering the query or returned data. -/
def adapter (limit : Nat) : QueryImpl BitOracleMachine.spec (OracleComp (spec limit)) :=
  fun q => Subtype.val <$> liftM ((spec limit).query q)

/-- Source termination and raw cost on all allowed answer branches. This is an
algorithmic obligation, not an execution-correspondence certificate. -/
def Within {s l m : Nat} (limit bound : Nat) :
    OracleComp BitOracleMachine.spec (BitOracleMachine.Config s l m × Nat) → Prop
  | .pure out => out.1.l = none ∧ out.2 ≤ bound
  | .liftBind q next => ∀ answer, Allowed limit q answer → Within limit bound (next answer)

private theorem run_halted {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (fuel : Nat) (cfg : BitOracleMachine.Config s l m) (h : cfg.l = none) :
    BitOracleLoop.run code fuel (.ready cfg) = pure (.ready cfg) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [BitOracleLoop.run, BitOracleLoop.step, h, pure_bind, ih]

private theorem spent_le {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (oa : OracleComp BitOracleMachine.spec (BitOracleMachine.Config s l m × Nat))
    (limit bound spent : Nat) (cfg : State s l m)
    (h : Realizes code oa spent cfg) (hw : Within limit bound oa) :
    spent ≤ 11 * bound := by
  induction oa generalizing spent cfg with
  | pure out => obtain ⟨used, hu, _⟩ := h; obtain ⟨_, hc⟩ := hw; omega
  | queryBind q next ih =>
    obtain ⟨before, continuation, _, hr⟩ := h
    let answer := defaultAnswer limit q
    have hb := ih answer.val (spent + before) (continuation answer.val)
      (hr answer.val) (hw answer.val answer.property)
    omega

private theorem simulate_node {α : Type} {M : Type → Type} [Monad M]
    (handler : QueryImpl BitOracleMachine.spec M) (q : BitOracleMachine.Request)
    (next : BitOracleMachine.spec.Range q → OracleComp BitOracleMachine.spec α) :
    simulateQ handler (OracleComp.queryBind q next) =
      (handler q >>= fun a => simulateQ handler (next a)) := rfl

/-- A common observation clock reproduces the entire allowed query tree.
Halted leaves absorb remaining ticks; running boundaries cannot be padded. -/
theorem realizes_run {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (oa : OracleComp BitOracleMachine.spec (BitOracleMachine.Config s l m × Nat))
    (limit bound spent : Nat) (cfg : State s l m)
    (h : Realizes code oa spent cfg) (hw : Within limit bound oa) :
    simulateQ (adapter limit) (BitOracleLoop.run code (11 * bound - spent) cfg) =
      (fun out => State.ready out.1) <$> simulateQ (adapter limit) oa := by
  induction oa generalizing spent cfg with
  | pure out =>
    obtain ⟨used, hu, he⟩ := h
    obtain ⟨hh, hb⟩ := hw
    have hn : 11 * bound - spent = used + (11 * bound - spent - used) := by omega
    rw [hn, BitOracleLoop.run_add, he, pure_bind, run_halted code _ _ hh]
    change pure (State.ready out.1) = (fun out => State.ready out.1) <$> pure out
    rfl
  | queryBind q next ih =>
    obtain ⟨before, continuation, he, hr⟩ := h
    let answer := defaultAnswer limit q
    have hb := spent_le code (next answer.val) limit bound (spent + before)
      (continuation answer.val) (hr answer.val) (hw answer.val answer.property)
    have hn : 11 * bound - spent = before + (11 * bound - (spent + before)) := by omega
    rw [hn, BitOracleLoop.run_add, he]
    simp only [simulateQ_bind, simulate_node, simulateQ_pure,
      adapter, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    apply bind_congr
    intro a
    have hi := ih a.val (spent + before) (continuation a.val)
      (hr a.val) (hw a.val a.property)
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using hi

/-- Actual source code supplies its execution witness. Only termination/cost
under the encoded-answer contract remain as explicit algorithmic premises. -/
theorem run_source {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (sourceFuel limit bound : Nat) (cfg : BitOracleMachine.Config s l m)
    (hw : Within limit bound (BitOracleMachine.run code sourceFuel cfg)) :
    simulateQ (adapter limit) (BitOracleLoop.run code (11 * bound) (.ready cfg)) =
      (fun out => State.ready out.1) <$>
        simulateQ (adapter limit) (BitOracleMachine.run code sourceFuel cfg) := by
  simpa only [Nat.sub_zero] using realizes_run code _ limit bound 0 (.ready cfg)
    (BitOracleLoop.run_source code sourceFuel cfg) hw

/-- Exact transport through any lawful handler, including probabilistic stateful
ones. The handler receives every original raw request. -/
theorem run_source_handler {s l m : Nat} {M : Type → Type} [Monad M] [LawfulMonad M]
    (code : BitOracleMachine.Code s l m) (sourceFuel limit bound : Nat)
    (cfg : BitOracleMachine.Config s l m)
    (hw : Within limit bound (BitOracleMachine.run code sourceFuel cfg))
    (handler : QueryImpl (spec limit) M) :
    simulateQ handler (simulateQ (adapter limit)
      (BitOracleLoop.run code (11 * bound) (.ready cfg))) =
      (fun out => State.ready out.1) <$>
        simulateQ handler (simulateQ (adapter limit) (BitOracleMachine.run code sourceFuel cfg)) := by
  rw [run_source code sourceFuel limit bound cfg hw, simulateQ_map]

end ExplainableCrypto.Helios.Computational.BitOracleLoopBounded
