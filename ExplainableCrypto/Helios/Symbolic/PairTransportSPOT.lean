import ExplainableCrypto.Helios.Symbolic.PairMinimumTransport
import ExplainableCrypto.Helios.Symbolic.PairTransportExperiments

namespace ExplainableCrypto.Helios.Symbolic.PairTransportSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world := LocalRootSPOT.world
abbrev rebuild : Recipe 3 := .binary .pair ((Term.var 1).project 0) ((Term.var 1).drop 1)
abbrev oneNames := ProofObservationSPOT.oneNames
abbrev oneLeft := ProofObservationSPOT.oneLeft
abbrev oneRight := ProofObservationSPOT.oneRight
abbrev oneWorld := ProofObservationSPOT.oneWorld
abbrev onePair : Recipe 3 := .binary .pair ((Term.var 1).project 1) (.const .bottom)

/-- The minimized gate failure: two minimum children form a five-node pair
whose shared shorter representative is the one-node honest ballot handle. -/
theorem reconstructed_ballot (swap : Bool) :
    Frame.MinimumChildren (world swap) rebuild ∧
    ¬ MinimalRecipe names.restricted (world swap).value rebuild ∧
    Frame.SharedMinimum (world swap) (world (!swap)) rebuild ∧
    EqE ((world swap).eval rebuild) ((world swap).eval (.var 1)) ∧
    EqE ((world (!swap)).eval rebuild) ((world (!swap)).eval (.var 1)) ∧
    rebuild.nodeCount = 5 := by
  have ha := minimum_ciphertext_selector names HistoricalFrameSPOT.fixture_names_fresh swap left right 0 0
  have hb := minimum_ballot_tail names HistoricalFrameSPOT.fixture_names_fresh swap left right 0 1 (by decide)
  have hv := (PairObservationSPOT.constructed_pair_and_truncation swap).2.2.1
  exact ⟨⟨ha,hb⟩,fun hm => hm.no_smaller (s := .var 1) trivial hv (by decide),
    minimum_children_pair_shared names HistoricalFrameSPOT.fixture_names_fresh swap (!swap) left right _ _ ha hb,
    hv,(PairObservationSPOT.constructed_pair_and_truncation (!swap)).2.2.1,rfl⟩

/-- Nonempty minimum tail aliases have exact syntax. At the empty boundary,
literal bottom is a minimum alias and is not the indexed chain. -/
theorem nonempty_origin_and_empty_boundary (swap : Bool) :
    (∀ k, k < 5 → ∀ r, MinimalRecipe names.restricted (world swap).value r →
      EqE ((world swap).eval r) ((world swap).eval ((Term.var 1).drop k)) →
      r = (Term.var 1).drop k) ∧
    MinimalRecipe names.restricted (world swap).value (.const .bottom) ∧
    EqE ((world swap).eval (.const .bottom)) ((world swap).eval ((Term.var 1).drop 5)) ∧
    (Term.const .bottom : Recipe 3) ≠ (Term.var 1).drop 5 :=
  ⟨fun k hk r hm he => minimum_honest_tail_origin names HistoricalFrameSPOT.fixture_names_fresh swap left right r hm 0 k hk he,
    .of_nodeCount_one trivial rfl,(PairObservationSPOT.empty_tails_coincide swap).2.1.symm,by decide⟩

private theorem one_pair_value (swap : Bool) :
    EqE ((oneWorld swap).eval onePair) ((oneWorld swap).eval ((Term.var 1).drop 2)) := by
  apply (pair_equality_iff_projections _ _ _
    (ballot_tail_pair_value oneNames swap oneLeft oneRight 0 2 (by decide))).mpr
  refine ⟨(ProofObservationSPOT.one_candidate_fields_coincide swap).2,?_⟩
  have hv := ballot_tail_recipe_value oneNames swap oneLeft oneRight 0 3 (by decide)
  have hl : (ballotFields oneNames 0 (choice swap oneLeft oneRight 0).value).length = 3 :=
    ballot_fields_length _ _ _
  have he : EqE ((oneWorld swap).eval ((Term.var 1).drop 3)) (.const .bottom) := by
    have hempty : (ballotFields oneNames 0 (choice swap oneLeft oneRight 0).value).drop 3 = [] :=
      List.drop_eq_nil_of_le (by rw [hl])
    rw [hempty] at hv
    exact hv
  exact he.symm

/-- Rebuilding the last one-candidate tail must allow the shorter component
proof in place of its aggregate field. Both minimum children share the tail. -/
theorem one_candidate_reconstruction (swap : Bool) :
    Frame.MinimumChildren (oneWorld swap) onePair ∧
    Frame.SharedMinimum (oneWorld swap) (oneWorld (!swap)) onePair ∧
    EqE ((oneWorld swap).eval onePair) ((oneWorld swap).eval ((Term.var 1).drop 2)) ∧
    EqE ((oneWorld (!swap)).eval onePair) ((oneWorld (!swap)).eval ((Term.var 1).drop 2)) ∧
    ¬ MinimalRecipe oneNames.restricted (oneWorld swap).value onePair := by
  have ha := minimum_component_proof_selector oneNames NumericReflectionSPOT.fixture_names_fresh swap oneLeft oneRight 0 0
  have hb : MinimalRecipe oneNames.restricted (oneWorld swap).value (.const .bottom) := .of_nodeCount_one trivial rfl
  exact ⟨⟨ha,hb⟩,minimum_children_pair_shared oneNames NumericReflectionSPOT.fixture_names_fresh swap (!swap)
      oneLeft oneRight _ _ ha hb,one_pair_value swap,one_pair_value (!swap),
    fun hm => hm.no_smaller ((ProjectionChain.drop (1 : Fin 3) 2).isPublic _) (one_pair_value swap) (by decide)⟩

/-- The field bound k+1 is sharp: field 2 has a three-node representative,
refuting the uniform stronger bound k+2. -/
theorem one_candidate_field_bound_sharp (swap : Bool) :
    EqE ((oneWorld swap).eval ((Term.var 1).project 1)) ((oneWorld swap).eval ((Term.var 1).project 2)) ∧
    3 ≤ ((Term.var 1 : Recipe 3).project 1).nodeCount ∧
    ¬ 4 ≤ ((Term.var 1 : Recipe 3).project 1).nodeCount := by
  have he := (ProofObservationSPOT.one_candidate_fields_coincide swap).2
  exact ⟨he,honest_field_public_size_bound oneNames NumericReflectionSPOT.fixture_names_fresh swap oneLeft oneRight _
    ((ProjectionChain.project (1 : Fin 3) 1).isPublic _) 0 2 (by decide) he,by decide⟩

/-- Public literal pairs instantiate shared transport and preserve ordered,
distinct members; the model has no universal pair eta rule for names. -/
theorem literal_pair_order_and_eta (swap : Bool) :
    Frame.SharedMinimum (world swap) (world (!swap)) (.binary .pair (.name 40) (.name 41)) ∧
    ¬ EqE (Term.binary (V := Empty) .pair (.name 40) (.name 41)) (.binary .pair (.name 41) (.name 40)) ∧
    ¬ EqE (Term.name (V := Empty) 40) (.binary .pair (.unary .fst (.name 40)) (.unary .snd (.name 40))) := by
  have ha : MinimalRecipe names.restricted (world swap).value (.name 40) :=
    .of_nodeCount_one (by change 40 ∉ names.restricted; decide) rfl
  have hb : MinimalRecipe names.restricted (world swap).value (.name 41) :=
    .of_nodeCount_one (by change 41 ∉ names.restricted; decide) rfl
  refine ⟨minimum_children_pair_shared names HistoricalFrameSPOT.fixture_names_fresh swap (!swap) left right _ _ ha hb,
    ?_,PairObservationSPOT.pair_value_premise_required⟩
  intro he
  have h := (EqE.name_iff 40 41).mp ((EqE.pair_iff _ _ _ _).mp he).1
  omega

/-- Without freshness a different one-node minimum handle equals an honest
nonempty tail, directly refuting exact minimum-tail origin. -/
theorem tail_origin_freshness_required :
    let ns := ProofObservationSPOT.colliding
    let φ := frame ns false right right
    MinimalRecipe ns.restricted φ.value (.var 2) ∧
    EqE (φ.eval (.var 2)) (φ.eval (.var 1)) ∧
    (Term.var 2 : Recipe 3) ≠ .var 1 ∧ ¬ ns.Fresh :=
  ⟨.of_nodeCount_one trivial rfl,.refl _,by decide,ProofObservationSPOT.freshness_required.2⟩

/-- The reduced criterion is inhabited on diagonal votes and retains distinct
public name tests. This does not assert its different-vote premises. -/
theorem crypto_arithmetic_transport_diagonal :
    Frame.StaticEq (frame names false left left) (frame names true left left) ∧
    ¬ EqE ((frame names true left left).eval (.name 40)) ((frame names true left left).eval (.name 41)) := by
  have h : Frame.CryptoArithmeticRootTransport (frame names false left left) (frame names true left left) := by
    intro r hp _ _ _
    obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (frame names false left left).value) r hp
    exact ⟨m,hm,he,he⟩
  exact ⟨staticEq_of_crypto_arithmetic_transport names HistoricalFrameSPOT.fixture_names_fresh left left h h,
    LocalRootSPOT.remaining_transport_diagonal.2⟩

end ExplainableCrypto.Helios.Symbolic.PairTransportSPOT
