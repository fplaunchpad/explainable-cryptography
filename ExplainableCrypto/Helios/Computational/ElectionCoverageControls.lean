import ExplainableCrypto.Helios.Computational.QueryClock
import ExplainableCrypto.Helios.Computational.EfficiencyInputControls
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
Independent controls for input-dependent query bounds and source query clocks.

The candidate is that a derived reached-input bound makes clocking transparent;
the adjacent falsifier has one more input element than the selected cap. Literal
query counters distinguish the original and truncated trees. The width two used
below is a generic fixture, not an assertion about actual election inputs.
These controls count source queries; they make no machine-runtime or PPT claim.
-/
namespace ExplainableCrypto.Helios.Computational.ElectionCoverageControls
open OracleComp OracleSpec EfficiencyInputControls

def InputQueryBounded (P : Polynomial Nat)
    (callback : List Bool → OracleComp coinSpec Unit) : Prop :=
  ∀ n input, (callback input).IsTotalQueryBound (P.eval (n + input.length))

/-- The same fixed callback admits a polynomial in parameter plus actual input size. -/
theorem linear_input_bound : InputQueryBounded Polynomial.X requestOncePerElement := by
  intro n input
  rw [Polynomial.eval_X, exact_query_budget]
  omega

/-- A sufficient reached-width cap preserves every dependent query and return. -/
theorem bounded_width_preserves (width : Nat) (input : List Bool)
    (h : input.length ≤ width) :
    QueryClock.clock width () (requestOncePerElement input) = requestOncePerElement input :=
  QueryClock.eq_of_total_bound width () _ ((exact_query_budget input width).mpr h)

theorem width_two_preserves (input : List Bool) (h : input.length ≤ 2) :
    QueryClock.clock 2 () (requestOncePerElement input) = requestOncePerElement input :=
  bounded_width_preserves 2 input h

private def queryCounter : QueryImpl coinSpec (StateT Nat Id) :=
  fun _ count => (false, count + 1)

/-- Independently predicted literal counts include both queries, not immediate fallback. -/
theorem two_element_counter :
    (simulateQ queryCounter
      (QueryClock.clock 2 () (requestOncePerElement [true, false]))).run 0 = ((), 2) := rfl

/-- The over-wide original makes three requests; its clocked prefix makes exactly two. -/
theorem overwide_counter :
    (simulateQ queryCounter (requestOncePerElement [true, false, true])).run 0 = ((), 3) ∧
    (simulateQ queryCounter
      (QueryClock.clock 2 () (requestOncePerElement [true, false, true]))).run 0 = ((), 2) :=
  ⟨rfl, rfl⟩

theorem overwide_tree_changes :
    QueryClock.clock 2 () (requestOncePerElement [true, false, true]) ≠
      requestOncePerElement [true, false, true] := by
  intro h
  have hc := congrArg (fun oa => (simulateQ queryCounter oa).run 0) h
  rw [overwide_counter.1, overwide_counter.2] at hc
  cases hc

def extraRequest (input : List Bool) : OracleComp coinSpec Unit := do
  let _ ← liftM (coinSpec.query ())
  requestOncePerElement input

/-- A nearby source that emits one extra query fails the declared input-length budget. -/
theorem extra_request_excluded (input : List Bool) :
    ¬ (extraRequest input).IsTotalQueryBound input.length := by
  change ¬ (requestOncePerElement (false :: input)).IsTotalQueryBound input.length
  rw [exact_query_budget]
  simp

theorem extra_request_not_linear_class : ¬ InputQueryBounded Polynomial.X extraRequest := by
  intro h
  have hzero := h 0 []
  simp only [List.length_nil, Nat.add_zero, Polynomial.eval_X] at hzero
  exact extra_request_excluded [] hzero

/-- Input-dependent admissibility does not retroactively give the original a global cap. -/
theorem original_still_has_no_global_cap :
    ¬ ∃ budget : Nat, ∀ input : List Bool,
      (requestOncePerElement input).IsTotalQueryBound budget :=
  no_uniform_input_cap

abbrev repeatedHashSpec : OracleSpec Unit := fun _ => Bool

/-- Both initial queries name the same sole key. An inconsistent answer pair
enables one extra request. This is a finite bound control, not an asymptotic claim. -/
def consistencySensitive : OracleComp repeatedHashSpec Unit := do
  let first ← liftM (repeatedHashSpec.query ())
  let second ← liftM (repeatedHashSpec.query ())
  if first = second then pure () else do
    let _ ← liftM (repeatedHashSpec.query ())
    pure ()

private def fixedHashCounter (answer : Bool) : QueryImpl repeatedHashSpec (StateT Nat Id) :=
  fun _ count => (answer, count + 1)

private def inconsistentHashCounter : QueryImpl repeatedHashSpec (StateT Nat Id) :=
  fun _ count => (decide (count = 0), count + 1)

/-- Every fixed function on the singleton key gives exactly the predicted two requests. -/
theorem fixed_hash_two_requests (answer : Bool) :
    (simulateQ (fixedHashCounter answer) consistencySensitive).run 0 = ((), 2) := by
  cases answer <;> rfl

/-- The independently chosen true/false/false response sequence reaches the extra request. -/
theorem inconsistent_hash_three_requests :
    (simulateQ inconsistentHashCounter consistencySensitive).run 0 = ((), 3) := rfl

/-- The same cap of two valid under each fixed handler is false for the complete query tree. -/
theorem consistent_bound_not_syntactic_bound :
    consistencySensitive.IsTotalQueryBound 3 ∧
      ¬ consistencySensitive.IsTotalQueryBound 2 := by
  constructor
  · unfold consistencySensitive
    rw [isTotalQueryBound_query_bind_iff]
    refine ⟨by decide, fun first => ?_⟩
    rw [isTotalQueryBound_query_bind_iff]
    refine ⟨by decide, fun second => ?_⟩
    by_cases he : first = second
    · simp only [he, ↓reduceIte]
      trivial
    · simp only [he, ↓reduceIte]
      exact ⟨by decide, fun _ => trivial⟩
  · intro h
    have hthird := h.2 true |>.2 false
    exact Nat.not_lt_zero _ hthird.1

#print axioms linear_input_bound
#print axioms bounded_width_preserves
#print axioms width_two_preserves
#print axioms two_element_counter
#print axioms overwide_counter
#print axioms overwide_tree_changes
#print axioms extra_request_excluded
#print axioms extra_request_not_linear_class
#print axioms original_still_has_no_global_cap
#print axioms fixed_hash_two_requests
#print axioms inconsistent_hash_three_requests
#print axioms consistent_bound_not_syntactic_bound
end ExplainableCrypto.Helios.Computational.ElectionCoverageControls
