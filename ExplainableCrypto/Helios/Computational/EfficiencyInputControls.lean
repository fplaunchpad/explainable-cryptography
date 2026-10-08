import VCVio.OracleComp.QueryTracking.QueryBound

/-!
Input-sensitive query bounds do not imply a finite bound over all input words.

Candidate implication: a callback with one query per input element admits a
single finite query cap on every input. The falsifier for cap `N` is a literal
word of length `N + 1`; the empty and singleton controls distinguish the boundary.
The formal oracle is the existing syntactic `IsTotalQueryBound`. Independently,
the source loop issues one coin request and removes one list element each time.
No machine runtime or standard-PPT membership theorem is asserted here.
-/
namespace ExplainableCrypto.Helios.Computational.EfficiencyInputControls
open OracleComp OracleSpec

def requestOncePerElement : List Bool → OracleComp coinSpec Unit
  | [] => pure ()
  | _ :: rest => do
      let _ ← liftM (coinSpec.query ())
      requestOncePerElement rest

/-- The least admissible query budget is exactly the input length. -/
theorem exact_query_budget (input : List Bool) (budget : Nat) :
    (requestOncePerElement input).IsTotalQueryBound budget ↔ input.length ≤ budget := by
  induction input generalizing budget with
  | nil => simp [requestOncePerElement, IsTotalQueryBound, IsQueryBound]
  | cons bit rest ih =>
      rw [requestOncePerElement, isTotalQueryBound_query_bind_iff]
      simp only [ih, List.length_cons]
      constructor
      · rintro ⟨hpos, hrest⟩
        have := hrest false
        omega
      · intro h
        exact ⟨by omega, fun _ => by omega⟩

theorem no_uniform_input_cap :
    ¬ ∃ budget : Nat, ∀ input : List Bool,
      (requestOncePerElement input).IsTotalQueryBound budget := by
  rintro ⟨budget, h⟩
  have hlong := (exact_query_budget (List.replicate (budget + 1) false) budget).mp
    (h (List.replicate (budget + 1) false))
  simp only [List.length_replicate] at hlong
  omega

theorem empty_control : requestOncePerElement [] = pure () ∧
    (requestOncePerElement []).IsTotalQueryBound 0 := by
  exact ⟨rfl, (exact_query_budget [] 0).mpr (by decide)⟩

theorem singleton_control :
    requestOncePerElement [true] = (do
      let _ ← liftM (coinSpec.query ())
      pure ()) ∧
    (requestOncePerElement [true]).IsTotalQueryBound 1 ∧
    ¬ (requestOncePerElement [true]).IsTotalQueryBound 0 := by
  refine ⟨rfl, (exact_query_budget [true] 1).mpr (by decide), ?_⟩
  rw [exact_query_budget]
  decide

#print axioms exact_query_budget
#print axioms no_uniform_input_cap
#print axioms empty_control
#print axioms singleton_control
end ExplainableCrypto.Helios.Computational.EfficiencyInputControls
