import ExplainableCrypto.Helios.Symbolic.CompleteProjectionTransport
import ExplainableCrypto.Helios.Symbolic.CiphertextSelectorExperiments

namespace ExplainableCrypto.Helios.Symbolic.CompleteProjectionSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world := LocalRootSPOT.world

/-- Both actual ciphertext fields have exact minima, and any minimum alias of
an honest ciphertext is the same indexed selector. -/
theorem indexed_ciphertext_minima (swap : Bool) :
    MinimalRecipe names.restricted (world swap).value ((Term.var 1).project 0) ∧
    MinimalRecipe names.restricted (world swap).value ((Term.var 1).project 1) ∧
    ((Term.var 1 : Recipe 3).project 0).nodeCount = 2 ∧
    ((Term.var 1 : Recipe 3).project 1).nodeCount = 3 ∧
    (∀ r, MinimalRecipe names.restricted (world swap).value r →
      EqE ((world swap).eval r) (ciphertext names 0 (choice swap left right 0).value 1) →
      r = (Term.var 1).project 1) :=
  ⟨minimum_ciphertext_selector names HistoricalFrameSPOT.fixture_names_fresh swap left right 0 0,
    minimum_ciphertext_selector names HistoricalFrameSPOT.fixture_names_fresh swap left right 0 1,
    rfl, rfl, fun r hm he => minimum_honest_ciphertext_origin names
      HistoricalFrameSPOT.fixture_names_fresh swap left right r hm 0 1 he⟩

/-- The gate's nonce collision has a smaller public equal ciphertext selector;
valid abstention alone cannot replace freshness. -/
theorem ciphertext_freshness_required (swap : Bool) :
    ¬ ProofObservationSPOT.colliding.Fresh ∧
    ¬ MinimalRecipe ProofObservationSPOT.colliding.restricted
      (frame ProofObservationSPOT.colliding swap right right).value ((Term.var 1).project 1) := by
  let ns := ProofObservationSPOT.colliding
  have he : EqE ((frame ns swap right right).eval ((Term.var 1).project 1))
      ((frame ns swap right right).eval ((Term.var 1).project 0)) := by
    cases swap with
    | false =>
      exact (combination_value ns false right right (.leaf (0,1))).trans
        (combination_value ns false right right (.leaf (0,0))).symm
    | true =>
      exact (combination_value ns true right right (.leaf (0,1))).trans
        (combination_value ns true right right (.leaf (0,0))).symm
  exact ⟨ProofObservationSPOT.freshness_required.2,
    fun hm => hm.no_smaller ((ProjectionChain.project (1 : Fin 3) 0).isPublic _) he (by decide)⟩

/-- A singleton is an actual honest leaf. Duplicate occurrences and a public
constructed contribution cannot disappear during grouping. -/
theorem singleton_preserves_contributions :
    (CiphertextAssembly.honest (n := 1) (handles := 3) (0,0)).group = .honest (.leaf (0,0)) ∧
    (Combination.mul (.leaf (0 : Nat)) (.leaf 0)).indices ≠ (Combination.leaf 0).indices ∧
    (CiphertextAssembly.mul (.honest (n := 1) (handles := 3) (0,0)) (.honest (0,0))).group ≠ .honest (.leaf (0,0)) ∧
    (CiphertextAssembly.mul (.honest (n := 1) (handles := 3) (0,0))
      (.constructed (.var 0) (.name 40) (.const .zero))).group ≠ .honest (.leaf (0,0)) := by
  exact ⟨rfl, by decide, by decide, by decide⟩

/-- Every nonempty tail, including the ciphertext prefix, is minimum. The empty
chain is longer than its literal bottom value but still has a shared minimum. -/
theorem all_tails_and_empty_boundary (swap : Bool) :
    (∀ k, k < 5 → MinimalRecipe names.restricted (world swap).value ((Term.var 1).drop k)) ∧
    (∀ k, k ≤ 5 → Frame.SharedMinimum (world swap) (world (!swap)) ((Term.var 1).drop k)) ∧
    ¬ MinimalRecipe names.restricted (world swap).value ((Term.var 1).drop 5) := by
  refine ⟨fun k hk => minimum_ballot_tail names HistoricalFrameSPOT.fixture_names_fresh swap left right 0 k hk,
    fun k hk => ballot_tail_shared_minimum names HistoricalFrameSPOT.fixture_names_fresh swap (!swap) left right 0 k hk, ?_⟩
  intro hm
  exact hm.no_smaller (s := .const .bottom) trivial
    (PairObservationSPOT.empty_tails_coincide swap).2.1 (by decide)

/-- Both selectors at every nonempty honest tail are covered in the actual
swapped frames, including ciphertext fields, proof fields and empty output. -/
theorem all_honest_tail_projections (swap : Bool) (k : Nat) (hk : k < 5) :
    Frame.SharedMinimum (world swap) (world (!swap)) (.unary .fst ((Term.var 1).drop k)) ∧
    Frame.SharedMinimum (world swap) (world (!swap)) (.unary .snd ((Term.var 1).drop k)) := by
  have hm := minimum_ballot_tail names HistoricalFrameSPOT.fixture_names_fresh swap left right 0 k hk
  exact ⟨minimum_child_projection_shared names HistoricalFrameSPOT.fixture_names_fresh swap (!swap) left right
    .fst (Or.inl rfl) _ hm,
    minimum_child_projection_shared names HistoricalFrameSPOT.fixture_names_fresh swap (!swap) left right
    .snd (Or.inr rfl) _ hm⟩

/-- At one candidate the last nonempty tail is minimum, but its first field is
not: the aggregate projection shares a shorter component representative. -/
theorem one_candidate_boundary (swap : Bool) :
    Frame.SharedMinimum (ProofObservationSPOT.oneWorld swap) (ProofObservationSPOT.oneWorld (!swap))
      (.unary .fst ((Term.var 1).drop 2)) ∧
    Frame.SharedMinimum (ProofObservationSPOT.oneWorld swap) (ProofObservationSPOT.oneWorld (!swap))
      (.unary .snd ((Term.var 1).drop 2)) ∧
    ¬ MinimalRecipe ProofObservationSPOT.oneNames.restricted (ProofObservationSPOT.oneWorld swap).value
      ((Term.var 1).project 2) := by
  have hm := minimum_ballot_tail ProofObservationSPOT.oneNames NumericReflectionSPOT.fixture_names_fresh swap
    ProofObservationSPOT.oneLeft ProofObservationSPOT.oneRight 0 2 (by decide)
  exact ⟨minimum_child_projection_shared _ NumericReflectionSPOT.fixture_names_fresh swap (!swap) _ _
      .fst (Or.inl rfl) _ hm,
    minimum_child_projection_shared _ NumericReflectionSPOT.fixture_names_fresh swap (!swap) _ _
      .snd (Or.inr rfl) _ hm,
    (ProjectionTransportSPOT.single_candidate_aggregate_not_minimum swap).2⟩

/-- The reduced obligation still includes real nonminimum arithmetic roots. -/
theorem remaining_case_nonempty (swap : Bool) :
    let r : Recipe 3 := .binary .add (.const .zero) (.const .zero)
    Frame.NonprojectionRootCase (world swap) r ∧ Frame.MinimumChildren (world swap) r ∧
    ¬ MinimalRecipe names.restricted (world swap).value r ∧
    Frame.SharedMinimum (world swap) (world (!swap)) r := by
  have h := LocalRootSPOT.remaining_numeric_case swap (world (!swap))
  exact ⟨trivial,h.1,h.2.2.1,h.2.2.2⟩

/-- Diagonal assignments inhabit the reduced criterion and still distinguish
public names. This does not discharge the different-vote premises. -/
theorem nonprojection_transport_diagonal :
    Frame.StaticEq (frame names false left left) (frame names true left left) ∧
    ¬ EqE ((frame names true left left).eval (.name 40)) ((frame names true left left).eval (.name 41)) := by
  have h : Frame.NonprojectionRootTransport (frame names false left left) (frame names true left left) := by
    intro r hp _ _ _
    obtain ⟨m, hm, he⟩ := exists_minimal_recipe (σ := (frame names false left left).value) r hp
    exact ⟨m,hm,he,he⟩
  exact ⟨staticEq_of_nonprojection_transport names HistoricalFrameSPOT.fixture_names_fresh left left h h,
    LocalRootSPOT.remaining_transport_diagonal.2⟩

end ExplainableCrypto.Helios.Symbolic.CompleteProjectionSPOT
