import ExplainableCrypto.Helios.Computational.BitOracleTapeLoop
import VCVio.OracleComp.Coinductive.DynSystem

/-! Source-derived query-tree correspondence for the actual tape loop.
The stopping witnesses are proofs, not executable callbacks or assumed adapters. -/
namespace ExplainableCrypto.Helios.Computational.BitOracleTapeLoop
open Turing OracleComp OracleSpec BitOraclePortTransfer OracleTapeOutput

private theorem query_normalize {α : Type} (q : BitOracleMachine.Request)
    (k : BitOracleMachine.spec.Range q → OracleComp BitOracleMachine.spec α) :
    (do let a ← liftM (BitOracleMachine.spec.query q); k a) = OracleComp.queryBind q k := rfl

/-- Every source query is an actual tape-loop query with the same complete
answer tree. Leaves retain the full caller and canonical work/query boundary.
This qualitative correspondence does not assert a common or polynomial clock. -/
def Realizes {s l m : Nat} (code : BitOracleMachine.Code s l m) :
    OracleComp BitOracleMachine.spec (BitOracleMachine.Config s l m) → State s l m → Prop
  | .pure out, cfg => ∃ used previous answer,
      run code used cfg = pure (ready out (wordTape previous) answer)
  | .liftBind query next, cfg => ∃ before,
      ∃ continuation : BitOracleMachine.spec.Range query → State s l m,
      run code before cfg = OracleComp.queryBind query (fun answer => pure (continuation answer)) ∧
      ∀ answer, Realizes code (next answer) (continuation answer)

private theorem realizes_prefix {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (oa : OracleComp BitOracleMachine.spec (BitOracleMachine.Config s l m))
    (used : Nat) (cfg mid : State s l m)
    (he : run code used cfg = pure mid) (h : Realizes code oa mid) : Realizes code oa cfg := by
  cases oa with
  | pure out =>
    obtain ⟨after, previous, answer, hr⟩ := h
    refine ⟨used + after, previous, answer, ?_⟩
    rw [run_add, he, pure_bind, hr]
  | queryBind q next =>
    obtain ⟨before, continuation, hr, ht⟩ := h
    refine ⟨used + before, continuation, ?_, ht⟩
    rw [run_add, he, pure_bind, hr]

private theorem source_hash {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (fuel : Nat) (cfg : BitOracleMachine.Config s l m) (source : Fin l)
    (request destination : Fin s) (next : Fin l)
    (hl : cfg.l = some source) (hc : code source = .hash request destination next) :
    Prod.fst <$> BitOracleMachine.run code (fuel + 1) cfg =
      (do let answer ← liftM (BitOracleMachine.spec.query (.hash (cfg.stk request)))
          Prod.fst <$> BitOracleMachine.run code fuel (BitOracleMachine.resume cfg destination next answer)) := by
  simp only [BitOracleMachine.run, BitOracleMachine.step, hl, hc,
    bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def]

private theorem source_coin {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (fuel : Nat) (cfg : BitOracleMachine.Config s l m) (source : Fin l)
    (destination : Fin s) (next : Fin l)
    (hl : cfg.l = some source) (hc : code source = .coin destination next) :
    Prod.fst <$> BitOracleMachine.run code (fuel + 1) cfg =
      (do let bit ← liftM (BitOracleMachine.spec.query .coin)
          Prod.fst <$> BitOracleMachine.run code fuel (BitOracleMachine.resume cfg destination next [bit])) := by
  simp only [BitOracleMachine.run, BitOracleMachine.step, hl, hc,
    bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def]

/-- Every finite original source execution has a derived execution in the
actual tape loop. All raw requests and answers are retained; arbitrary local
statements, early halt, aliased ports and successor private frames are covered.
No execution, presentation or termination certificate is supplied by the caller. -/
theorem run_source {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (fuel : Nat) (cfg : BitOracleMachine.Config s l m) (previous : List Bool)
    (oldAnswer : Tape (Option Bool)) :
    Realizes code (Prod.fst <$> BitOracleMachine.run code fuel cfg)
      (ready cfg (wordTape previous) oldAnswer) := by
  induction fuel generalizing cfg previous oldAnswer with
  | zero => exact ⟨0, previous, oldAnswer, rfl⟩
  | succ fuel ih =>
    cases hl : cfg.l with
    | none =>
      simpa only [BitOracleMachine.run, BitOracleMachine.step, hl, pure_bind,
        Nat.zero_add, Prod.mk.eta, bind_pure] using ih cfg previous oldAnswer
    | some source =>
      cases hc : code source with
      | compute stmt =>
        obtain ⟨used, _, he⟩ := compute_run code cfg source stmt hl hc (wordTape previous) oldAnswer
        have h := realizes_prefix code _ used _ _ he
          (ih (TM2.stepAux stmt cfg.var cfg.stk) previous oldAnswer)
        simpa only [BitOracleMachine.run, BitOracleMachine.step, hl, hc, pure_bind,
          map_bind, map_pure, map_eq_bind_pure_comp, Function.comp_def, bind_assoc] using h
      | hash request destination next =>
        obtain ⟨before, _, he⟩ := hash_issue code cfg source request destination next hl hc previous oldAnswer
        rw [source_hash code fuel cfg source request destination next hl hc, query_normalize]
        refine ⟨before, (fun answer => .call .hash (BitOracleTapeCall.incoming cfg request destination next answer)),
          (by simpa only [query_normalize] using he), ?_⟩
        intro answer
        obtain ⟨used, _, hr⟩ := reply_run code .hash cfg request destination next
          (cfg.stk request) (wordTape (cfg.stk request)) answer
        have h := realizes_prefix code _ used _ _ hr
          (ih (BitOracleMachine.resume cfg destination next answer) (cfg.stk request) (wordTape answer))
        change Realizes code (Prod.fst <$> BitOracleMachine.run code fuel
          (BitOracleMachine.resume cfg destination next answer))
          (.call .hash (BitOracleTapeCall.incoming cfg request destination next answer))
        exact h
      | coin destination next =>
        have he := coin_issue code cfg source destination next hl hc (wordTape previous) oldAnswer
        rw [source_coin code fuel cfg source destination next hl hc, query_normalize]
        refine ⟨2, (fun bit => .call .coin (BitOracleTapeCall.received cfg destination destination next []
          (wordTape previous) [bit])), (by simpa only [query_normalize] using he), ?_⟩
        intro bit
        obtain ⟨used, _, hr⟩ := reply_run code .coin cfg destination destination next [] (wordTape previous) [bit]
        have h := realizes_prefix code _ used _ _ hr
          (ih (BitOracleMachine.resume cfg destination next [bit]) previous (wordTape [bit]))
        change Realizes code (Prod.fst <$> BitOracleMachine.run code fuel
          (BitOracleMachine.resume cfg destination next [bit]))
          (.call .coin (BitOracleTapeCall.received cfg destination destination next [] (wordTape previous) [bit]))
        exact h

/-- Each source path occurs in a finite actual tape execution with the same
complete query/answer log and final caller. Stopping times may depend on answers. -/
theorem realizes_path {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (oa : OracleComp BitOracleMachine.spec (BitOracleMachine.Config s l m))
    (cfg : State s l m) (h : Realizes code oa cfg) (path : PFunctor.FreeM.Path oa) :
    ∃ used previous answer, ∃ actual : PFunctor.FreeM.Path (run code used cfg),
      PFunctor.FreeM.output (run code used cfg) actual =
        ready (PFunctor.FreeM.output oa path) (wordTape previous) answer ∧
      logOfPath (run code used cfg) actual = logOfPath oa path := by
  induction oa generalizing cfg with
  | pure out =>
    obtain ⟨used, previous, answer, he⟩ := h
    refine ⟨used, previous, answer, ?_⟩
    rw [he]
    exact ⟨⟨⟩, rfl, rfl⟩
  | queryBind q next ih =>
    rcases path with ⟨answer, tail⟩
    obtain ⟨before, continuation, he, hr⟩ := h
    obtain ⟨used, previous, finalAnswer, actual, ho, ht⟩ :=
      ih answer (continuation answer) (hr answer) tail
    refine ⟨before + used, previous, finalAnswer, ?_⟩
    rw [run_add, he]
    change ∃ actual : PFunctor.FreeM.Path
        (OracleComp.queryBind q (fun a => run code used (continuation a))),
      PFunctor.FreeM.output _ actual = ready (PFunctor.FreeM.output (next answer) tail)
        (wordTape previous) finalAnswer ∧
      logOfPath _ actual = (⟨q, answer⟩ :: logOfPath (next answer) tail)
    refine ⟨⟨answer, actual⟩, ho, ?_⟩
    exact congrArg (List.cons ⟨q, answer⟩) ht

end ExplainableCrypto.Helios.Computational.BitOracleTapeLoop
