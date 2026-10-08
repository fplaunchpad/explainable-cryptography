import ExplainableCrypto.Helios.Computational.BitOracleLoop
import VCVio.OracleComp.Coinductive.DynSystem

/-! Costed execution correspondence for every finite raw source run.
The witness is a proof about the fixed loop, never an executable callback or
part of its state. Native query nodes must agree as complete OracleComp trees.
Observation times may depend on answers already received. -/
namespace ExplainableCrypto.Helios.Computational.BitOracleLoop
open OracleComp OracleSpec Turing.TM2
open BitOraclePortTransfer

private theorem query_normalize {α : Type} (q : BitOracleMachine.Request)
    (k : BitOracleMachine.spec.Range q → OracleComp BitOracleMachine.spec α) :
    (do let a ← liftM (BitOracleMachine.spec.query q); k a) = OracleComp.queryBind q k := rfl

/-- Actual loop execution realizes a finite source tree. Each query boundary
is an equality of complete query/continuation programs. Leaves retain every
caller stack and pay for all preceding micro steps against the source charge.
This is a metatheoretic stopping witness, not a standard-machine cost theorem. -/
def Realizes {s l m : Nat} (code : BitOracleMachine.Code s l m) :
    OracleComp BitOracleMachine.spec (BitOracleMachine.Config s l m × Nat) →
      Nat → State s l m → Prop
  | .pure out, spent, cfg => ∃ used,
      spent + used ≤ 11 * out.2 ∧ run code used cfg = pure (.ready out.1)
  | .liftBind query next, spent, cfg => ∃ before,
      ∃ continuation : BitOracleMachine.spec.Range query → State s l m,
      run code before cfg = OracleComp.queryBind query (fun answer => pure (continuation answer)) ∧
      ∀ answer, Realizes code (next answer) (spent + before) (continuation answer)

private theorem realizes_weaken {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (oa : OracleComp BitOracleMachine.spec (BitOracleMachine.Config s l m × Nat))
    (spent small : Nat) (cfg : State s l m) (h : Realizes code oa spent cfg)
    (hle : small ≤ spent) : Realizes code oa small cfg := by
  induction oa generalizing spent small cfg with
  | pure out =>
    obtain ⟨used, hu, he⟩ := h
    exact ⟨used, by omega, he⟩
  | queryBind q next ih =>
    obtain ⟨before, continuation, he, hr⟩ := h
    exact ⟨before, continuation, he, fun a => ih a _ _ _ (hr a) (by omega)⟩

/-- Internal blocks compose without adding, dropping or reordering queries. -/
private theorem realizes_prefix {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (oa : OracleComp BitOracleMachine.spec (BitOracleMachine.Config s l m × Nat))
    (spent used : Nat) (cfg mid : State s l m)
    (he : run code used cfg = pure mid)
    (h : Realizes code oa (spent + used) mid) : Realizes code oa spent cfg := by
  cases oa with
  | pure out =>
    obtain ⟨after, ha, hr⟩ := h
    refine ⟨used + after, by omega, ?_⟩
    rw [run_add, he, pure_bind, hr]
  | queryBind q next =>
    obtain ⟨before, continuation, hr, ht⟩ := h
    refine ⟨used + before, continuation, ?_, ?_⟩
    · rw [run_add, he, pure_bind, hr]
    · intro a
      simpa only [Nat.add_assoc] using ht a

/-- Prepending a source charge permits the corresponding accumulated work. -/
private theorem realizes_shift {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (oa : OracleComp BitOracleMachine.spec (BitOracleMachine.Config s l m × Nat))
    (spent charge : Nat) (cfg : State s l m) (h : Realizes code oa spent cfg) :
    Realizes code ((fun out => (out.1, charge + out.2)) <$> oa)
      (11 * charge + spent) cfg := by
  induction oa generalizing spent cfg with
  | pure out =>
    obtain ⟨used, hu, he⟩ := h
    exact ⟨used, by simp only [Nat.mul_add]; omega, he⟩
  | queryBind q next ih =>
    obtain ⟨before, continuation, he, hr⟩ := h
    refine ⟨before, continuation, he, ?_⟩
    intro a
    change Realizes code ((fun out => (out.1, charge + out.2)) <$> next a)
      ((11 * charge + spent) + before) (continuation a)
    simpa only [Nat.add_assoc] using ih a (spent + before) (continuation a) (hr a)

private theorem localCost_pos {s l m : Nat}
    (stmt : Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m)) :
    0 < BitOracleMachine.localCost stmt := by
  cases stmt <;> simp [BitOracleMachine.localCost]

/-- Every bounded raw source program has an actual loop execution with its
entire query tree and terminal caller configuration preserved. Every branch
costs at most eleven times that branch's raw charge; no response-length bound
or caller-supplied correspondence is assumed. -/
theorem run_source {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (fuel : Nat) (cfg : BitOracleMachine.Config s l m) :
    Realizes code (BitOracleMachine.run code fuel cfg) 0 (.ready cfg) := by
  induction fuel generalizing cfg with
  | zero => exact ⟨0, by simp, rfl⟩
  | succ fuel ih =>
    cases hl : cfg.l with
    | none =>
      simpa only [BitOracleMachine.run, BitOracleMachine.step, hl, pure_bind,
        Nat.zero_add, Prod.mk.eta, bind_pure] using ih cfg
    | some label =>
      cases hc : code label with
      | compute stmt =>
        have hs : step code (.ready cfg) = pure (.ready (stepAux stmt cfg.var cfg.stk)) := by
          simp only [step, hl, hc]
        have shifted := realizes_shift code _ 0 (BitOracleMachine.localCost stmt) _
          (ih (stepAux stmt cfg.var cfg.stk))
        have small := realizes_weaken code _ _ 1 _ shifted (by
          have := localCost_pos stmt
          omega)
        have result := realizes_prefix code _ 0 1 (.ready cfg) _
          (by simpa only [run, bind_pure] using hs) small
        simpa only [BitOracleMachine.run, BitOracleMachine.step, hl, hc, pure_bind,
          map_eq_bind_pure_comp, Function.comp_def] using result
      | hash source destination next =>
        obtain ⟨before, he, after⟩ := hash_cycle code cfg label source destination next hl hc
        simp only [BitOracleMachine.run, BitOracleMachine.step, hl, hc, query_normalize]
        refine ⟨before, (fun answer => .response destination (start cfg destination next answer)),
          (by simpa only [query_normalize] using he), ?_⟩
        intro answer
        obtain ⟨used, hu, hr⟩ := after answer
        have shifted := realizes_shift code _ 0
          (1 + (cfg.stk source).length + (cfg.stk destination).length + answer.length) _
          (ih (BitOracleMachine.resume cfg destination next answer))
        have small := realizes_weaken code _ _ (before + used) _ shifted (by omega)
        have result := realizes_prefix code _ before used _ _ hr small
        simp only [Nat.zero_add]
        change Realizes code (do
          let out ← BitOracleMachine.run code fuel (BitOracleMachine.resume cfg destination next answer)
          pure (out.1, 1 + (cfg.stk source).length + (cfg.stk destination).length + answer.length + out.2))
          before (.response destination (start cfg destination next answer))
        simpa only [map_eq_bind_pure_comp, Function.comp_def] using result
      | coin destination next =>
        obtain ⟨he, after⟩ := coin_cycle code cfg label destination next hl hc
        simp only [BitOracleMachine.run, BitOracleMachine.step, hl, hc, query_normalize]
        refine ⟨1, (fun bit => .response destination (start cfg destination next [bit])),
          ?_, ?_⟩
        · simpa only [run, bind_pure, query_normalize] using he
        · intro bit
          obtain ⟨used, hu, hr⟩ := after bit
          have shifted := realizes_shift code _ 0 (2 + (cfg.stk destination).length) _
            (ih (BitOracleMachine.resume cfg destination next [bit]))
          have small := realizes_weaken code _ _ (1 + used) _ shifted (by omega)
          have result := realizes_prefix code _ 1 used _ _ hr small
          change Realizes code (do
            let out ← BitOracleMachine.run code fuel (BitOracleMachine.resume cfg destination next [bit])
            pure (out.1, 2 + (cfg.stk destination).length + out.2))
            1 (.response destination (start cfg destination next [bit]))
          simpa only [map_eq_bind_pure_comp, Function.comp_def] using result

/-- Read a costed execution witness using the pinned library's typed paths and
query logs. Every selected source path occurs in the actual micro-step runner
with the same query/answer log and complete terminal caller state. -/
theorem realizes_path {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (oa : OracleComp BitOracleMachine.spec (BitOracleMachine.Config s l m × Nat))
    (spent : Nat) (cfg : State s l m) (h : Realizes code oa spent cfg)
    (path : PFunctor.FreeM.Path oa) :
    ∃ used, spent + used ≤ 11 * (PFunctor.FreeM.output oa path).2 ∧
      ∃ actual : PFunctor.FreeM.Path (run code used cfg),
        PFunctor.FreeM.output (run code used cfg) actual =
          .ready (PFunctor.FreeM.output oa path).1 ∧
        logOfPath (run code used cfg) actual = logOfPath oa path := by
  induction oa generalizing spent cfg with
  | pure out =>
    obtain ⟨used, hu, he⟩ := h
    refine ⟨used, hu, ?_⟩
    rw [he]
    exact ⟨⟨⟩, rfl, rfl⟩
  | queryBind q next ih =>
    rcases path with ⟨answer, tail⟩
    obtain ⟨before, continuation, he, hr⟩ := h
    obtain ⟨used, hu, actual, ho, ht⟩ := ih answer (spent + before)
      (continuation answer) (hr answer) tail
    refine ⟨before + used, ?_, ?_⟩
    · change spent + (before + used) ≤ 11 * (PFunctor.FreeM.output (next answer) tail).2
      omega
    rw [run_add, he]
    change ∃ actual : PFunctor.FreeM.Path
        (OracleComp.queryBind q (fun a => run code used (continuation a))),
      PFunctor.FreeM.output _ actual = .ready (PFunctor.FreeM.output (next answer) tail).1 ∧
      logOfPath _ actual = (⟨q, answer⟩ :: logOfPath (next answer) tail)
    refine ⟨⟨answer, actual⟩, ho, ?_⟩
    exact congrArg (List.cons ⟨q, answer⟩) ht

/-- Direct path-level consequence for every finite source execution, with no
execution or cost certificate supplied by its caller. -/
theorem run_source_path {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (fuel : Nat) (cfg : BitOracleMachine.Config s l m)
    (path : PFunctor.FreeM.Path (BitOracleMachine.run code fuel cfg)) :
    ∃ used, used ≤ 11 * (PFunctor.FreeM.output (BitOracleMachine.run code fuel cfg) path).2 ∧
      ∃ actual : PFunctor.FreeM.Path (run code used (.ready cfg)),
        PFunctor.FreeM.output (run code used (.ready cfg)) actual =
          .ready (PFunctor.FreeM.output (BitOracleMachine.run code fuel cfg) path).1 ∧
        logOfPath (run code used (.ready cfg)) actual =
          logOfPath (BitOracleMachine.run code fuel cfg) path := by
  simpa only [Nat.zero_add] using
    realizes_path code _ 0 (.ready cfg) (run_source code fuel cfg) path

end ExplainableCrypto.Helios.Computational.BitOracleLoop
