import ExplainableCrypto.Helios.Symbolic.ProjectionMinimumTransport
import ExplainableCrypto.Helios.Symbolic.ProjectionTransportExperiments
import ExplainableCrypto.Helios.Symbolic.MinimumTransportSPOT

namespace ExplainableCrypto.Helios.Symbolic.ProjectionTransportSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world := LocalRootSPOT.world
abbrev oneNames := ProofObservationSPOT.oneNames
abbrev oneLeft := ProofObservationSPOT.oneLeft
abbrev oneRight := ProofObservationSPOT.oneRight
abbrev oneWorld := ProofObservationSPOT.oneWorld

/-- Actual two-candidate component and aggregate selectors attain sizes four,
five and six, despite arbitrary E-equivalent candidate representations. -/
theorem indexed_proof_minima (swap : Bool) :
    MinimalRecipe names.restricted (world swap).value ((Term.var 1).project 2) ∧
    MinimalRecipe names.restricted (world swap).value ((Term.var 1).project 3) ∧
    MinimalRecipe names.restricted (world swap).value ((Term.var 1).project 4) ∧
    ((Term.var 1 : Recipe 3).project 2).nodeCount = 4 ∧
    ((Term.var 1 : Recipe 3).project 3).nodeCount = 5 ∧
    ((Term.var 1 : Recipe 3).project 4).nodeCount = 6 :=
  ⟨minimum_component_proof_selector names HistoricalFrameSPOT.fixture_names_fresh swap left right 0 0,
    minimum_component_proof_selector names HistoricalFrameSPOT.fixture_names_fresh swap left right 0 1,
    minimum_aggregate_proof_selector names HistoricalFrameSPOT.fixture_names_fresh (by decide) swap left right 0,
    rfl,rfl,rfl⟩

/-- The shrunk gate failure has an actual smaller public equal recipe. -/
theorem single_candidate_aggregate_not_minimum (swap : Bool) :
    EqE ((oneWorld swap).eval ((Term.var 1).project 2)) ((oneWorld swap).eval ((Term.var 1).project 1)) ∧
    ¬ MinimalRecipe oneNames.restricted (oneWorld swap).value ((Term.var 1).project 2) := by
  have he := (ProofObservationSPOT.one_candidate_fields_coincide swap).2.symm
  exact ⟨he, fun hm => hm.no_smaller ((ProjectionChain.project (1 : Fin 3) 1).isPublic _) he (by decide)⟩

/-- The nonminimum aggregate chain still has a shared minimum via the general
proof-chain theorem; no input minimum judgment is supplied to that theorem. -/
theorem single_candidate_chain_shared (swap : Bool) :
    Frame.SharedMinimum (oneWorld swap) (oneWorld (!swap)) ((Term.var 1).project 2) ∧
    MinimalRecipe oneNames.restricted (oneWorld swap).value ((Term.var 1).project 1) ∧
    MinimalRecipe oneNames.restricted (oneWorld swap).value ((Term.var 1).drop 2) := by
  exact ⟨proof_chain_shared_minimum oneNames NumericReflectionSPOT.fixture_names_fresh swap (!swap)
    oneLeft oneRight 1 (.project 1 2) (aggregate_proof_recipe_value oneNames swap oneLeft oneRight 0),
    minimum_component_proof_selector oneNames NumericReflectionSPOT.fixture_names_fresh swap oneLeft oneRight 0 0,
    minimum_proof_tail oneNames NumericReflectionSPOT.fixture_names_fresh swap oneLeft oneRight 0 2 (by decide) (by decide)⟩

/-- Colliding component nonces make the later selector nonminimum, so freshness
is essential even though all vote substitutions are valid. -/
theorem selector_freshness_required :
    ¬ ProofObservationSPOT.colliding.Fresh ∧
    ¬ MinimalRecipe ProofObservationSPOT.colliding.restricted
      (frame ProofObservationSPOT.colliding false right right).value ((Term.var 1).project 3) := by
  let ns := ProofObservationSPOT.colliding
  have he : EqE ((frame ns false right right).eval ((Term.var 1).project 3))
      ((frame ns false right right).eval ((Term.var 1).project 2)) :=
    (component_proof_recipe_value ns false right right 0 1).trans
      (component_proof_recipe_value ns false right right 0 0).symm
  exact ⟨ProofObservationSPOT.freshness_required.2,
    fun hm => hm.no_smaller ((ProjectionChain.project (1 : Fin 3) 2).isPublic _) he (by decide)⟩

/-- Both selectors of a real minimum explicit pair get shared representatives;
the selected values differ, ruling out constant projection output. -/
theorem explicit_pair_selection :
    Frame.SharedMinimum MinimumTransportSPOT.emptyFrame MinimumTransportSPOT.emptyFrame
      (.unary .fst MinimumTransportSPOT.minimumPair) ∧
    Frame.SharedMinimum MinimumTransportSPOT.emptyFrame MinimumTransportSPOT.emptyFrame
      (.unary .snd MinimumTransportSPOT.minimumPair) ∧
    ¬ EqE (Term.name (V := Empty) 40) (.name 41) := by
  refine ⟨.projection_of_minimum_pair _ _ MinimumTransportSPOT.literal_pair_minimum .fst (Or.inl rfl),
    .projection_of_minimum_pair _ _ MinimumTransportSPOT.literal_pair_minimum .snd (Or.inr rfl), ?_⟩
  intro he
  have hn := (EqE.name_iff 40 41).mp he
  omega

/-- Nonempty proof suffixes are minimum, but the full empty chain has a shorter
bottom representative. Both are shared across the actual different-vote swap. -/
theorem proof_suffix_and_empty_boundary (swap : Bool) :
    (∀ k, 2 ≤ k → k < 5 → MinimalRecipe names.restricted (world swap).value ((Term.var 1).drop k)) ∧
    (∀ k, 2 ≤ k → k ≤ 5 → Frame.SharedMinimum (world swap) (world (!swap)) ((Term.var 1).drop k)) ∧
    ¬ MinimalRecipe names.restricted (world swap).value ((Term.var 1).drop 5) := by
  refine ⟨fun k hlo hhi => minimum_proof_tail names HistoricalFrameSPOT.fixture_names_fresh swap left right 0 k hlo hhi,
    fun k hlo hhi => proof_tail_shared_minimum names HistoricalFrameSPOT.fixture_names_fresh swap (!swap) left right 0 k hlo hhi, ?_⟩
  intro hm
  have he := (PairObservationSPOT.empty_tails_coincide swap).2.1
  exact hm.no_smaller (s := .const .bottom) trivial he (by decide)

/-- A proof-valued successful projection of a minimum honest suffix is solved
without any observation-induction premise. -/
theorem successful_proof_projection (swap : Bool) :
    Frame.SharedMinimum (world swap) (world (!swap))
      (.unary .fst ((Term.var 1).drop 2)) :=
  proof_projection_shared_minimum names HistoricalFrameSPOT.fixture_names_fresh swap (!swap) left right
    .fst (Or.inl rfl) _
    (minimum_proof_tail names HistoricalFrameSPOT.fixture_names_fresh swap left right 0 2 (by decide) (by decide))
    (component_proof_recipe_value names swap left right 0 0)

end ExplainableCrypto.Helios.Symbolic.ProjectionTransportSPOT
