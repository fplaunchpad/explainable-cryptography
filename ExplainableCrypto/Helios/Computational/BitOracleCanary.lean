import ExplainableCrypto.Helios.Computational.BitOracleMachine
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! A fixed four-label program for H(x), H(H(x)), H(x), with all answer words
retained. The cost is ghost instrumentation for the proposed raw-port contract;
standard oracle-machine transfer/compilation costs remain an adequacy obligation. -/
namespace ExplainableCrypto.Helios.Computational.BitOracleCanary
open OracleComp OracleSpec BitOracleMachine

/-- No program field depends on the input word or security parameter. -/
def code : Code 4 4 1 := ![.hash 0 1 1, .hash 1 2 2, .hash 0 3 3, .compute .halt]

def initial (word : List Bool) : Config 4 4 1 :=
  ⟨some 0, 0, ![word, [], [], []]⟩

def final (word a b c : List Bool) : Config 4 4 1 :=
  ⟨none, 0, ![word, a, b, c]⟩

def source (word : List Bool) : OracleComp spec (Config 4 4 1 × Nat) := do
  let a ← liftM (spec.query (.hash word))
  let b ← liftM (spec.query (.hash a))
  let c ← liftM (spec.query (.hash word))
  pure (final word a b c, 4 + 2 * word.length + 2 * a.length + b.length + c.length)

/-- Exact query tree, halted full configuration and derived length charge. -/
theorem run_source (word : List Bool) : run code 4 (initial word) = source word := by
  simp [run, step, code, initial, resume, localCost, source, Function.update]
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  apply bind_congr
  intro a
  apply bind_congr
  intro b
  apply bind_congr
  intro c
  apply congrArg (pure : Config 4 4 1 × Nat → OracleComp spec (Config 4 4 1 × Nat))
  apply Prod.ext
  · apply congrArg (fun tapes => (⟨none, 0, tapes⟩ : Config 4 4 1))
    funext j
    fin_cases j <;> rfl
  · omega

end ExplainableCrypto.Helios.Computational.BitOracleCanary
