import ExplainableCrypto.Helios.Symbolic.RemainingRootTransport
import ExplainableCrypto.Helios.Symbolic.LocalRootExperiments

namespace ExplainableCrypto.Helios.Symbolic.LocalRootSPOT
open Historical General
abbrev names := ObservationAssemblySPOT.names
abbrev left := ObservationAssemblySPOT.left
abbrev right := ObservationAssemblySPOT.right
abbrev world := ObservationAssemblySPOT.world
abbrev partialRecipe : Recipe 3 := .binary .partialDecrypt (.var 0) (.var 1)
abbrev key : Recipe 3 := .unary .pk partialRecipe
abbrev proof : Recipe 3 := .spk key partialRecipe (.var 1) (.var 2)

private theorem handle_minimum (swap : Bool) (i : Fin 3) :
    MinimalRecipe names.restricted (world swap).value (.var i) :=
  .of_nodeCount_one trivial rfl

/-- Nested non-atomic minimum children produce a ten-node minimum proof. Its
source-minimum syntax is a shared representative in every destination frame. -/
theorem nested_constructor_minima (swap : Bool) :
    MinimalRecipe names.restricted (world swap).value partialRecipe ∧
    MinimalRecipe names.restricted (world swap).value key ∧
    MinimalRecipe names.restricted (world swap).value proof ∧ proof.nodeCount = 10 ∧
    ∀ ψ : Frame names.restricted 3, Frame.SharedMinimum (world swap) ψ proof := by
  have hp := minimum_partial_of_children names swap left right _ _ (handle_minimum swap 0) (handle_minimum swap 1)
  have hk := minimum_pk_of_child names swap left right _ hp
  have hs := minimum_spk_of_children names swap left right _ _ _ _ hk hp
    (handle_minimum swap 1) (handle_minimum swap 2)
  exact ⟨hp, hk, hs, rfl, fun _ => .of_minimal hs⟩

/-- Source semantic failure, not raw matching, closes all three destructor families. -/
theorem stuck_parent_minima (swap : Bool) :
    MinimalRecipe names.restricted (world swap).value (.unary .fst (.var 0)) ∧
    MinimalRecipe names.restricted (world swap).value (.binary .dec (.var 0) (.name 40)) ∧
    MinimalRecipe names.restricted (world swap).value (.ternary .checkspk (.var 0) (.name 40) (.var 1)) := by
  have h40 : MinimalRecipe names.restricted (world swap).value (.name 40) :=
    .of_nodeCount_one (by change 40 ∉ names.restricted; decide) rfl
  have hdec : ∀ m, ¬ DecryptionMatch ((world swap).eval (.var 0)) (.name 40) m := by
    rintro m ⟨k, nonce, _, hc⟩
    have hh := ((name_irreducible 40).reducesModulo hc).head_eq
    cases hh
  have hcheck : ¬ ProofCheckMatch ((world swap).eval (.var 0)) (.name 40) ((world swap).eval (.var 1)) := by
    rintro ⟨k, nonce, bit, _, _, hc, _⟩
    have hh := ((name_irreducible 40).reducesModulo hc).head_eq
    cases hh
  exact ⟨minimum_stuck_projection_of_child names swap left right .fst (Or.inl rfl) _
      (handle_minimum swap 0) (fun x y => pk_not_eqE_pair _ x y),
    minimum_stuck_decryption_of_children names swap left right _ _ (handle_minimum swap 0) h40 hdec,
    minimum_stuck_check_of_children names swap left right _ _ _ (handle_minimum swap 0) h40
      (handle_minimum swap 1) hcheck⟩

/-- Weakening the same historical frame's policy admits a minimum secret-name
child whose pk parent has a smaller equivalent public handle. -/
theorem full_secret_policy_required (swap : Bool) :
    MinimalRecipe names.nonceNames (world swap).value (.name names.secretKey) ∧
    ¬ MinimalRecipe names.nonceNames (world swap).value (.unary .pk (.name names.secretKey)) := by
  refine ⟨.of_nodeCount_one (by change names.secretKey ∉ names.nonceNames; decide) rfl, ?_⟩
  intro hm
  exact hm.no_smaller (s := .var 0) trivial (.refl _) (by decide)

/-- Publishing a partial constructor breaks minimum-parent closure even with
literal minimum children. This artificial frame is not the initial historical frame. -/
theorem published_partial_breaks_closure :
    let φ := PartialDecryptionObservationSPOT.publishedFrame
    MinimalRecipe names.restricted φ.value (.name 40) ∧
    MinimalRecipe names.restricted φ.value (.name 50) ∧
    ¬ MinimalRecipe names.restricted φ.value (.binary .partialDecrypt (.name 40) (.name 50)) := by
  refine ⟨.of_nodeCount_one (by change 40 ∉ names.restricted; decide) rfl,
    .of_nodeCount_one (by change 50 ∉ names.restricted; decide) rfl, ?_⟩
  intro hm
  exact hm.no_smaller (s := .var 0) trivial (.refl _) (by decide)

/-- Dropping minimum size for a child permits an ordinary shorter pk recipe. -/
theorem minimum_child_required (swap : Bool) :
    let a : Recipe 3 := .unary .fst (.binary .pair (.name 40) (.const .bottom))
    a.Public names.restricted ∧
    ¬ MinimalRecipe names.restricted (world swap).value (.unary .pk a) := by
  have hp : (Term.name (V := Fin 3) 40).Public names.restricted := by change 40 ∉ names.restricted; decide
  refine ⟨⟨hp, trivial⟩, ?_⟩
  intro hm
  exact hm.no_smaller (s := .unary .pk (.name 40)) hp
    (.unary .pk (RootStep.fst _ _).sound) (by decide)

/-- The remaining-root interface is nonempty: numeric collapse has minimum
children, a genuinely smaller output, and an explicit shared representative. -/
theorem remaining_numeric_case (swap : Bool) (ψ : Frame names.restricted 3) :
    let r : Recipe 3 := .binary .add (.const .zero) (.const .zero)
    Frame.MinimumChildren (world swap) r ∧ Frame.RootTransportCase (world swap) r ∧
    ¬ MinimalRecipe names.restricted (world swap).value r ∧ Frame.SharedMinimum (world swap) ψ r := by
  have hz : MinimalRecipe names.restricted (world swap).value (.const .zero) := .of_nodeCount_one trivial rfl
  refine ⟨⟨hz,hz⟩, trivial, ?_, .of_recipe_eqE hz (.equation .zero_zero)⟩
  intro hm
  exact hm.no_smaller (s := .const .zero) trivial (.equation .zero_zero) (by decide)

/-- The reduced historical criterion is inhabited on diagonal assignments and
retains distinct public observations. The different-vote premises remain open. -/
theorem remaining_transport_diagonal :
    Frame.StaticEq (frame names false left left) (frame names true left left) ∧
    ¬ EqE ((frame names true left left).eval (.name 40)) ((frame names true left left).eval (.name 41)) := by
  have h : Frame.RemainingRootTransport (frame names false left left) (frame names true left left) := by
    intro r hp _ _ _
    obtain ⟨m, hm, he⟩ := exists_minimal_recipe (σ := (frame names false left left).value) r hp
    exact ⟨m, hm, he, he⟩
  refine ⟨staticEq_of_remaining_root_transport names HistoricalFrameSPOT.fixture_names_fresh left left h h, ?_⟩
  intro he
  have hn := (EqE.name_iff 40 41).mp he
  omega

end ExplainableCrypto.Helios.Symbolic.LocalRootSPOT
