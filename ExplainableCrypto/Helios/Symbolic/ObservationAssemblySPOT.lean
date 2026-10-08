import ExplainableCrypto.Helios.Symbolic.MinimumObservationAssembly
import ExplainableCrypto.Helios.Symbolic.ObservationAssemblyExperiments
import ExplainableCrypto.Helios.Symbolic.MultiplicationObservationSPOT
import ExplainableCrypto.Helios.Symbolic.MinimumOriginSPOT
import ExplainableCrypto.Helios.Symbolic.DecryptionPathSPOT
import ExplainableCrypto.Helios.Symbolic.ProofCheckPathSPOT

namespace ExplainableCrypto.Helios.Symbolic.ObservationAssemblySPOT
open Historical General
abbrev names := MultiplicationObservationSPOT.names
abbrev left := MultiplicationObservationSPOT.left
abbrev right := MultiplicationObservationSPOT.right
abbrev world := MultiplicationObservationSPOT.world
abbrev multiplied := MultiplicationObservationSPOT.multiplied

/-- The shrunk input-0 gate failure is a genuine E equation changing the raw head. -/
theorem raw_head_counterexample :
    let t : Ground := .unary .fst (.binary .pair (.name 40) (.name 41))
    EqE t (.name 40) ∧ ObservationAssemblyExperiments.branch t = 3 ∧
    ObservationAssemblyExperiments.branch (normalizeRaw t) = 0 := by
  exact ⟨(RootStep.fst _ _).sound, by decide, by decide⟩

/-- Concrete normal destructors instantiate all three exclusion lemmas. -/
theorem normal_destructors_no_match :
    (∀ a b, ¬ EqE (Term.name (V := Empty) 40) (.binary .pair a b)) ∧
    (∀ m, ¬ DecryptionMatch (Term.var (V := Nat) 0) DecryptionPathSPOT.stuckCipher m) ∧
    ¬ ProofCheckMatch (Term.var (V := Nat) 0) (.var 1) (.var 2) :=
  ⟨MinimumOriginSPOT.projected_name_irreducible.projection_no_pair (Or.inl rfl),
    DecryptionPathSPOT.stuck_irreducible.decryption_no_match,
    ProofCheckPathSPOT.stuck_irreducible.proof_check_no_match⟩

/-- Delayed E5, E6 and proof matches refute removing whole-term normality. -/
theorem delayed_matches_need_normality :
    ¬ Irreducible DecryptionPathSPOT.directSource ∧
    ¬ Irreducible DecryptionPathSPOT.partialSource ∧
    ¬ Irreducible (ProofCheckPathSPOT.delayed .zero) := by
  exact ⟨fun ht => ht.decryption_no_match _ DecryptionPathSPOT.delayed_direct_match,
    fun ht => ht.decryption_no_match _ DecryptionPathSPOT.delayed_partial_match,
    fun ht => ht.proof_check_no_match (ProofCheckPathSPOT.delayed_match .zero (Or.inl rfl))⟩

/-- Equal values need not have equal raw heads; E7 belongs to the ciphertext
normal-value branch even when the source has a multiplication head. -/
theorem fusion_changes_branch :
    let c : Ground := .ternary .penc (.name 40) (.name 41) (.const .zero)
    let t : Ground := .ternary .penc (.name 40) (.binary .compose (.name 41) (.name 41))
      (.binary .add (.const .zero) (.const .zero))
    EqE (.binary .mul c c) t ∧
    ObservationAssemblyExperiments.branch (.binary .mul c c) = 8 ∧
    ObservationAssemblyExperiments.branch t = 11 := by
  exact ⟨(RootStep.homomorphic _ _ _ _ _).sound, rfl, rfl⟩

/-- Distinct E0-equivalent minima instantiate the head-free assembly. The
bounded premise is supplied by diagonal candidate assignments. -/
theorem minimum_forward_permutation : multiplied 40 41 ≠ multiplied 41 40 ∧
    EqE ((frame names true left left).eval (multiplied 40 41))
      ((frame names true left left).eval (multiplied 41 40)) := by
  refine ⟨by decide, minimum_equality_forward names HistoricalFrameSPOT.fixture_names_fresh
    left left _ _ ?_ ?_ (CiphertextObservationSPOT.diagonal_observations _) ?_⟩
  · exact MultiplicationObservationSPOT.literal_mul_minimum false left left 40 41 (by decide) (by decide)
  · exact MultiplicationObservationSPOT.literal_mul_minimum false left left 41 40 (by decide) (by decide)
  · exact .equation (.comm .mul trivial _ _)

private theorem below_two (φ ψ : Frame names.restricted 3) : φ.ObservationsBelow ψ 2 := by
  intro r s _ _ hsize
  have := r.nodeCount_pos
  have := s.nodeCount_pos
  omega

/-- Different normal heads remain distinguishable in the actual different-vote
worlds. Both minima are established independently; the size-two premise is empty. -/
theorem minimum_cross_head_distinction :
    ¬ EqE ((world false).eval (.name 40)) ((world false).eval (.const .zero)) ∧
    (EqE ((world false).eval (.name 40)) ((world false).eval (.const .zero)) ↔
      EqE ((world true).eval (.name 40)) ((world true).eval (.const .zero))) := by
  have hn (swap : Bool) : MinimalRecipe names.restricted (world swap).value (.name 40) :=
    .of_nodeCount_one (by change 40 ∉ names.restricted; decide) rfl
  have hc (swap : Bool) : MinimalRecipe names.restricted (world swap).value (.const .zero) :=
    .of_nodeCount_one trivial rfl
  refine ⟨?_, minimum_equality_swap_of_both_minima names HistoricalFrameSPOT.fixture_names_fresh
    left right _ _ (hn false) (hc false) (hn true) (hc true) (below_two _ _)⟩
  intro he
  have hh := (EqE.ground_atoms_iff (.name 40) (.const .zero) rfl rfl).mp he
  cases hh

/-- A minimum honest handle may change its raw value across the swap while its
self-equality still transfers. This is one public test, not static equivalence. -/
theorem changed_handle_forward :
    (world false).value 1 ≠ (world true).value 1 ∧
    EqE ((world true).eval (.var 1)) ((world true).eval (.var 1)) := by
  have hm : MinimalRecipe names.restricted (world false).value (.var 1) :=
    .of_nodeCount_one trivial rfl
  exact ⟨by decide, minimum_equality_forward names HistoricalFrameSPOT.fixture_names_fresh
    left right _ _ hm hm (below_two _ _) (.refl _)⟩

/-- Both local minimization premises are inhabited on a diagonal frame; the
result still distinguishes public names. No different-vote transport is assumed. -/
theorem local_transport_diagonal :
    Frame.StaticEq (frame names false left left) (frame names true left left) ∧
    ¬ EqE ((frame names true left left).eval (.name 40))
      ((frame names true left left).eval (.name 41)) := by
  have hlocal : Frame.LocalMinimumTransport (frame names false left left) (frame names true left left) := by
    intro r hp _
    obtain ⟨m, hm, he⟩ := exists_minimal_recipe (σ := (frame names false left left).value) r hp
    exact ⟨m, hm, he, he⟩
  refine ⟨staticEq_of_local_transport_both names HistoricalFrameSPOT.fixture_names_fresh
    left left hlocal hlocal, ?_⟩
  intro he
  have hn := (EqE.name_iff 40 41).mp he
  omega

end ExplainableCrypto.Helios.Symbolic.ObservationAssemblySPOT
