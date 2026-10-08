import ExplainableCrypto.Helios.Symbolic.ExpandedMinimumLifting
import ExplainableCrypto.Helios.Symbolic.ExpandedObservationExperiments
import ExplainableCrypto.Helios.Symbolic.ExpandedAssemblySPOT
import ExplainableCrypto.Helios.Symbolic.MinimumTransportSPOT

namespace ExplainableCrypto.Helios.Symbolic.ExpandedObservationSPOT
open Historical General ObservationAssemblyExperiments
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []

private theorem below_two (φ ψ : Frame names.restricted (ExpandedHandles 1)) : φ.ObservationsBelow ψ 2 := by
  intro r s _ _ hsize
  have := r.nodeCount_pos
  have := s.nodeCount_pos
  omega

/-- The discovered gate failure is a real E0 alias: raw normalization leaves
the published result at an addition head although its full-E value is one. -/
theorem raw_normalization_misses_numeric_head (swap : Bool) :
    let t := (world swap).eval (.var (expandedResult 1))
    branch (normalizeRaw t) = 9 ∧ EqE t (.const .one) ∧
      ExpandedObservationExperiments.normalizedBranch t = 1 := by
  refine ⟨?_,SharedTallySPOT.nonliteral_two_candidate_tally.2 swap,?_⟩
  all_goals cases swap <;> decide

/-- The raw published result is an E6 decryption. Its checked full-E constant
value determines the comparison branch, not its public handle/raw value head. -/
theorem published_result_changes_head (swap : Bool) :
    let t := (world swap).eval (.var (expandedResult 0))
    branch t = 7 ∧ EqE t (.const .zero) ∧ branch (.const .zero) = 1 :=
  ⟨rfl,SharedTallySPOT.nonliteral_two_candidate_tally.1 swap,rfl⟩

/-- A repeated ciphertext uses the ciphertext normal-value branch even though
the public expression has a multiplication root. -/
theorem fused_product_changes_head :
    let c : Ground := .ternary .penc (.name 40) (.name 50) (.const .zero)
    let t : Ground := .ternary .penc (.name 40) (.binary .compose (.name 50) (.name 50))
      (.binary .add (.const .zero) (.const .zero))
    EqE (.binary .mul c c) t ∧ branch (.binary .mul c c) = 8 ∧ branch t = 11 :=
  ⟨(RootStep.homomorphic _ _ _ _ _).sound,rfl,rfl⟩

/-- The binding mutation remains a full-E no-match counterexample. Matching
the secret key and plaintext alone does not select a successful E6 branch. -/
theorem wrong_binding_stays_unmatched :
    ¬ (∃ m, DecryptionMatch (.binary .partialDecrypt (.name 40) (DecryptionProbeSPOT.cipher 51))
      (DecryptionProbeSPOT.cipher 50) m) := SharedTallySPOT.decryption_binding_required

/-- Distinct source-minimum recipes compare equal in different-vote worlds:
a published E6 result and its literal zero. No head certificate is supplied. -/
theorem minimum_forward_result_alias :
    (Term.var (expandedResult (n := 1) 0) : Recipe (ExpandedHandles 1)) ≠ .const .zero ∧
    EqE ((world true).eval (.var (expandedResult 0))) ((world true).eval (.const .zero)) := by
  refine ⟨by decide,accepted_expanded_minimum_equality_forward names HistoricalFrameSPOT.fixture_names_fresh
    left right [] (by simp) trivial _ _ (.of_nodeCount_one trivial rfl) (.of_nodeCount_one trivial rfl)
    (below_two _ _) (SharedTallySPOT.nonliteral_two_candidate_tally.1 false)⟩

/-- The assembled iff handles different normal heads without an equality
premise, retaining a separating public name/constant test in both worlds. -/
theorem minimum_cross_head_distinction :
    ¬ EqE ((world false).eval (.name 40)) ((world false).eval (.const .zero)) ∧
    (EqE ((world false).eval (.name 40)) ((world false).eval (.const .zero)) ↔
      EqE ((world true).eval (.name 40)) ((world true).eval (.const .zero))) := by
  have hn (swap : Bool) : MinimalRecipe names.restricted (world swap).value (.name 40) :=
    .of_nodeCount_one (by change 40 ∉ names.restricted; decide) rfl
  have hz (swap : Bool) : MinimalRecipe names.restricted (world swap).value (.const .zero) :=
    .of_nodeCount_one trivial rfl
  exact ⟨name_not_eqE_const 40 .zero,
    accepted_expanded_minimum_equality_swap_of_both_minima names HistoricalFrameSPOT.fixture_names_fresh
      left right [] (by simp) trivial _ _ (hn false) (hz false) (hn true) (hz true) (below_two _ _)⟩

/-- Reversed acceptance is inhabited by two distinct, sequentially accepted
adversarial ballots, not just by the empty list. -/
theorem reversed_nonempty_acceptance :
    SharedTallySPOT.submissions.length = 2 ∧
    (frame SharedTallySPOT.names false SharedTallySPOT.right SharedTallySPOT.left).AcceptsSequence
      0 (.var 0) honestBoardRecipes SharedTallySPOT.submissions := by
  refine ⟨rfl,accepted_sequence_reversed_candidates SharedTallySPOT.names NumericReflectionSPOT.fixture_names_fresh
    SharedTallySPOT.left SharedTallySPOT.right SharedTallySPOT.submissions ?_ (SharedTallySPOT.fresh_sequence_accepted false)⟩
  intro r hr
  simp [SharedTallySPOT.submissions] at hr
  have publicBallot (nonce : Nat) (bit : Constant) (hn : nonce ∉ SharedTallySPOT.names.restricted) :
      (ElectionTallyExperiments.publicBallot nonce bit).Public SharedTallySPOT.names.restricted := by
    apply constructorBallot_public
    · trivial
    · intro _; exact hn
    · intro _; trivial
    · intro _; exact ⟨trivial,hn,trivial,trivial,hn,trivial⟩
  rcases hr with rfl | rfl
  · exact publicBallot 40 .one (by decide)
  · exact publicBallot 41 .zero (by decide)

private theorem diagonal_minima :
    Frame.CommonMinima (expandedFrame names false left left []) (expandedFrame names true left left []) := by
  intro r hp
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (expandedFrame names false left left []).value) r hp
  exact ⟨m,hm,he,he⟩

/-- The bounded lifting interface is inhabited at every bound. It still
rejects unequal public names, so observations are not made universally true. -/
theorem bounded_two_way_lifting (bound : Nat) :
    Frame.ObservationsBelow (expandedFrame names false left left []) (expandedFrame names true left left []) bound ∧
    ¬ EqE ((expandedFrame names true left left []).eval (.name 40))
      ((expandedFrame names true left left []).eval (.name 41)) := by
  refine ⟨accepted_expanded_observationsBelow_of_two_way_minima names HistoricalFrameSPOT.fixture_names_fresh
    false true left left [] (by simp) trivial bound
    (fun r hp _ => diagonal_minima r hp) (fun r hp _ => diagonal_minima r hp),?_⟩
  intro he
  exact (by decide : 40 ≠ 41) ((EqE.name_iff 40 41).mp he)

/-- The exact final/partial-frame lifting has a nonconstant diagonal instance.
It does not supply two-way minima for different candidate assignments. -/
theorem final_and_partial_lifting :
    Frame.StaticEq (finalFrame names false left left []) (finalFrame names true left left []) ∧
    Frame.StaticEq (partialFrame names false left left []) (partialFrame names true left left []) ∧
    ¬ EqE ((finalFrame names true left left []).eval (.name 40))
      ((finalFrame names true left left []).eval (.name 41)) := by
  refine ⟨(accepted_final_staticEq_iff_expanded_common_minima names HistoricalFrameSPOT.fixture_names_fresh
    left left [] (by simp) trivial).mpr ⟨diagonal_minima,diagonal_minima⟩,
    (accepted_partial_staticEq_iff_expanded_common_minima names HistoricalFrameSPOT.fixture_names_fresh
      left left [] (by simp) trivial).mpr ⟨diagonal_minima,diagonal_minima⟩,?_⟩
  intro he
  exact (by decide : 40 ≠ 41) ((EqE.name_iff 40 41).mp he)

/-- A retained finite size/equality countermodel rejects dropping shared
transport from generic lifting. This finite model is not a Helios frame. -/
theorem minimum_step_alone_is_insufficient :
    MinimumTransportExperiments.step MinimumTransportExperiments.fixtureSize
      MinimumTransportExperiments.fixtureSource MinimumTransportExperiments.fixtureTarget = true ∧
    MinimumTransportExperiments.allTests MinimumTransportExperiments.fixtureSource
      MinimumTransportExperiments.fixtureTarget = false ∧
    MinimumTransportExperiments.shared MinimumTransportExperiments.fixtureSize
      MinimumTransportExperiments.fixtureSource MinimumTransportExperiments.fixtureTarget = false :=
  ⟨MinimumTransportSPOT.minimum_tests_need_transport.1,
    MinimumTransportSPOT.minimum_tests_need_transport.2.1,MinimumTransportSPOT.minimum_tests_need_transport.2.2.1⟩

end ExplainableCrypto.Helios.Symbolic.ExpandedObservationSPOT
