import ExplainableCrypto.Helios.Computational.TM2ReturnLink
import VCVio.OracleComp.SimSemantics.SimulateQ

/-! Fixed finite-control TM2 programs with explicit raw oracle ports.
Local instructions are the existing Mathlib stack machine. Oracle word transfer
is charged explicitly; a standard open-oracle adequacy theorem remains separate. -/
namespace ExplainableCrypto.Helios.Computational.BitOracleMachine
open OracleComp OracleSpec Turing.TM2

inductive Request where
  | coin
  | hash (word : List Bool)
  deriving DecidableEq

def spec : OracleSpec Request := fun r => match r with
  | .coin => Bool
  | .hash _ => List Bool

abbrev Config (ports labels memory : Nat) :=
  Cfg (fun _ : Fin ports => Bool) (Fin labels) (Fin memory)

/-- All local functions have finite domains. Unbounded words occur only on stacks. -/
inductive Command (ports labels memory : Nat) where
  | compute (stmt : Stmt (fun _ : Fin ports => Bool) (Fin labels) (Fin memory))
  | coin (destination : Fin ports) (next : Fin labels)
  | hash (request destination : Fin ports) (next : Fin labels)

/-- Fix this code once for the whole security-parameter family. -/
abbrev Code (ports labels memory : Nat) := Fin labels → Command ports labels memory

/-- A finite syntactic bound on the local operations in one TM2 statement. -/
def localCost {s l m : Nat} : Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m) → Nat
  | .push _ _ q | .peek _ _ q | .pop _ _ q | .load _ q => 1 + localCost q
  | .branch _ a b => 1 + max (localCost a) (localCost b)
  | .goto _ | .halt => 1

def resume {s l m : Nat} (cfg : Config s l m) (destination : Fin s)
    (next : Fin l) (answer : List Bool) : Config s l m :=
  ⟨some next, cfg.var, Function.update cfg.stk destination answer⟩

/-- Every stack other than the named response port is retained. -/
theorem resume_frame {s l m : Nat} (cfg : Config s l m) (destination other : Fin s)
    (next : Fin l) (answer : List Bool) (h : other ≠ destination) :
    (resume cfg destination next answer).stk other = cfg.stk other := by
  simp [resume, Function.update_of_ne h]

def step {s l m : Nat} (code : Code s l m) (cfg : Config s l m) :
    OracleComp spec (Config s l m × Nat) :=
  match cfg.l with
  | none => pure (cfg, 0)
  | some label => match code label with
    | .compute stmt => pure (stepAux stmt cfg.var cfg.stk, localCost stmt)
    | .coin destination next => do
      let bit ← liftM (spec.query .coin)
      pure (resume cfg destination next [bit], 2 + (cfg.stk destination).length)
    | .hash request destination next => do
      let answer ← liftM (spec.query (.hash (cfg.stk request)))
      pure (resume cfg destination next answer,
        1 + (cfg.stk request).length + (cfg.stk destination).length + answer.length)

/-- Fuel is an observation bound; the returned configuration reveals whether it halted. -/
def run {s l m : Nat} (code : Code s l m) : Nat → Config s l m →
    OracleComp spec (Config s l m × Nat)
  | 0, cfg => pure (cfg, 0)
  | fuel + 1, cfg => do
    let first ← step code cfg
    let rest ← run code fuel first.1
    pure (rest.1, first.2 + rest.2)

/-- Existing local TM2 code executes with exactly its original configuration transition. -/
theorem local_step {s l m : Nat}
    (code : Fin l → Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m)) (cfg : Config s l m) :
    Prod.fst <$> step (fun label => .compute (code label)) cfg =
      pure (TM2ReturnLink.tick code cfg) := by
  cases cfg with
  | mk label v tapes => cases label <;> rfl

/-- Every bounded deterministic run is the existing Mathlib TM2 run, without an adapter premise. -/
theorem local_run {s l m : Nat}
    (code : Fin l → Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m))
    (fuel : Nat) (cfg : Config s l m) :
    Prod.fst <$> run (fun label => .compute (code label)) fuel cfg =
      pure ((TM2ReturnLink.tick code)^[fuel] cfg) := by
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih =>
    cases cfg with
    | mk label v tapes =>
      cases label <;>
        simpa only [run, step, pure_bind, bind_assoc, map_bind, map_pure, map_eq_bind_pure_comp, Function.comp_def,
          Function.iterate_succ_apply,
          TM2ReturnLink.tick, Turing.TM2.step, Option.getD_some, Option.getD_none] using ih _

/-- A fixed bound on deterministic source statements derives the complete
run's charge and exact TM2 result. This supplies conversion/linking costs. -/
theorem compute_run_cost {s l m : Nat}
    (code : Fin l → Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m))
    (bound : Nat) (hc : ∀ label, localCost (code label) ≤ bound)
    (fuel : Nat) (cfg : Config s l m) :
    ∃ charge ≤ bound * fuel,
      run (fun label => .compute (code label)) fuel cfg =
        pure ((TM2ReturnLink.tick code)^[fuel] cfg, charge) := by
  induction fuel generalizing cfg with
  | zero => exact ⟨0, by omega, rfl⟩
  | succ fuel ih =>
    cases cfg with
    | mk label memory words =>
      cases label with
      | none =>
        obtain ⟨charge, hq, he⟩ := ih ⟨none, memory, words⟩
        refine ⟨charge, by rw [Nat.mul_succ]; omega, ?_⟩
        simp only [run, step, pure_bind, he, Nat.zero_add, Function.iterate_succ_apply,
          TM2ReturnLink.tick, Turing.TM2.step, Option.getD_none]
      | some label =>
        obtain ⟨charge, hq, he⟩ := ih (stepAux (code label) memory words)
        refine ⟨localCost (code label) + charge, ?_, ?_⟩
        · have := hc label
          rw [Nat.mul_succ]
          omega
        · simp only [run, step, pure_bind, he, Function.iterate_succ_apply,
            TM2ReturnLink.tick, Turing.TM2.step, Option.getD_some]

end ExplainableCrypto.Helios.Computational.BitOracleMachine
