import VCVio.OracleComp.QueryTracking.QueryBound

/-! A source-level query clock with an explicit fallback result. The clock counts every
oracle query, preserves pure returns at zero fuel, and truncates only a pending query.
It neither measures local computation time nor supplies a machine-efficiency certificate.
-/
namespace ExplainableCrypto.Helios.Computational.QueryClock
open OracleComp OracleSpec
universe u
variable {ι : Type u} {spec : OracleSpec.{u,u} ι} {α : Type u}

/-- Emit at most `fuel` original queries. Exhaustion at a pending query returns `fallback`;
a pure leaf is returned unchanged, including when the available fuel is zero. -/
def clock : Nat → α → OracleComp spec α → OracleComp spec α
  | _, _, .pure value => pure value
  | 0, fallback, .liftBind _ _ => pure fallback
  | fuel + 1, fallback, .liftBind query next =>
    .liftBind query (fun answer => clock fuel fallback (next answer))

@[simp] theorem clock_pure (fuel : Nat) (fallback value : α) :
    clock fuel fallback (pure value : OracleComp spec α) = pure value := by
  cases fuel <;> rfl

@[simp] theorem clock_query_zero (fallback : α) (query : spec.Domain)
    (next : spec.Range query → OracleComp spec α) :
    clock 0 fallback (liftM (spec.query query) >>= next) = pure fallback := rfl

@[simp] theorem clock_query_succ (fuel : Nat) (fallback : α) (query : spec.Domain)
    (next : spec.Range query → OracleComp spec α) :
    clock (fuel + 1) fallback (liftM (spec.query query) >>= next) =
      (do let answer ← liftM (spec.query query); clock fuel fallback (next answer)) := rfl

/-- The cap is global over all typed response paths, without an input-size or support premise. -/
theorem total_bound (fuel : Nat) (fallback : α) (oa : OracleComp spec α) :
    (clock fuel fallback oa).IsTotalQueryBound fuel := by
  induction oa using OracleComp.inductionOn generalizing fuel with
  | pure value => simp only [clock_pure]; trivial
  | query_bind query next ih =>
    cases fuel with
    | zero => rw [clock_query_zero]; trivial
    | succ fuel =>
      rw [clock_query_succ, isTotalQueryBound_query_bind_iff]
      exact ⟨Nat.succ_pos _, fun answer => by simpa using ih answer fuel⟩

/-- A sufficient cap preserves the complete original dependent query tree, not just its law. -/
theorem eq_of_total_bound (fuel : Nat) (fallback : α) (oa : OracleComp spec α)
    (h : oa.IsTotalQueryBound fuel) : clock fuel fallback oa = oa := by
  induction oa using OracleComp.inductionOn generalizing fuel with
  | pure value => exact clock_pure fuel fallback value
  | query_bind query next ih =>
    rw [isTotalQueryBound_query_bind_iff] at h
    cases fuel with
    | zero => exact (Nat.not_lt_zero _ h.1).elim
    | succ fuel =>
      rw [clock_query_succ]
      congr 1
      funext answer
      exact ih answer fuel (by simpa using h.2 answer)

/-- Hash queries, or any other selected class of oracle indices, inherit the same bound. -/
theorem predicate_bound (predicate : ι → Prop) [DecidablePred predicate]
    (fuel : Nat) (fallback : α) (oa : OracleComp spec α) :
    (clock fuel fallback oa).IsQueryBoundP predicate fuel :=
  (total_bound fuel fallback oa).isQueryBoundP (p := predicate)

namespace Controls
abbrev testSpec : OracleSpec Unit := fun _ => Bool
private def twice : OracleComp testSpec Bool := do
  let first ← liftM (testSpec.query ())
  let second ← liftM (testSpec.query ())
  pure (first && !second)

private def countTrue : QueryImpl testSpec (StateT Nat Id) :=
  fun _ count => (true, count + 1)

/-- Independent exact event counts distinguish capping from discarding the whole program. -/
theorem cap_preserves_prefix :
    (simulateQ countTrue (clock 1 true twice)).run 0 = (true, 1) := rfl

theorem uncapped_two_queries : (simulateQ countTrue twice).run 0 = (false, 2) := rfl

theorem enough_fuel_preserves_tree : clock 2 true twice = twice := by
  apply eq_of_total_bound
  exact ⟨by decide, fun _ => ⟨by decide, fun _ => trivial⟩⟩

theorem truncation_changes_tree : clock 1 true twice ≠ twice := by
  intro h
  have he := congrArg (fun oa => (simulateQ countTrue oa).run 0) h
  rw [cap_preserves_prefix, uncapped_two_queries] at he
  cases he

theorem truncation_is_not_immediate_fallback :
    clock 1 true twice ≠ (pure true : OracleComp testSpec Bool) := by
  intro h
  have he := congrArg (fun oa => (simulateQ countTrue oa).run 0) h
  rw [cap_preserves_prefix] at he
  have : (true, 1) = (true, 0) := he
  cases this

theorem pure_at_zero_keeps_original :
    clock 0 false (pure true : OracleComp testSpec Bool) = pure true := rfl

#print axioms cap_preserves_prefix
#print axioms uncapped_two_queries
#print axioms enough_fuel_preserves_tree
#print axioms truncation_changes_tree
#print axioms truncation_is_not_immediate_fallback
#print axioms pure_at_zero_keeps_original
end Controls

#print axioms total_bound
#print axioms eq_of_total_bound
#print axioms predicate_bound
end ExplainableCrypto.Helios.Computational.QueryClock
