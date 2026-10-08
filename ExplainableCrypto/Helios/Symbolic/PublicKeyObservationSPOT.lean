import ExplainableCrypto.Helios.Symbolic.PublicKeyObservationInduction
import ExplainableCrypto.Helios.Symbolic.ProofObservationSPOT

namespace ExplainableCrypto.Helios.Symbolic.PublicKeyObservationSPOT
open Historical General
abbrev names := ProofObservationSPOT.names
abbrev left := ProofObservationSPOT.left
abbrev right := ProofObservationSPOT.right
abbrev world := ProofObservationSPOT.world
abbrev freshKey : Recipe 3 := .unary .pk (.name 40)
abbrev handle : Recipe 3 := .var 0
abbrev wrapper : Recipe 3 := .unary .fst (.binary .pair handle (.const .bottom))

/-- The published key is an inhabited one-node minimum, in both actual worlds. -/
theorem published_key_minimum (swap : Bool) :
    MinimalRecipe names.restricted (world swap).value handle ∧
    handle.nodeCount = 1 ∧ EqE ((world swap).eval handle) (publicKey names) :=
  ⟨MinimalRecipe.of_nodeCount_one trivial rfl, rfl, .refl _⟩

/-- A different constructed key is an exact two-node minimum. Every possible
size-one competitor is excluded, including unbounded names and all handles. -/
theorem constructed_key_minimum (swap : Bool) (a b : CandidateSubstitution 1 Empty) :
    MinimalRecipe names.restricted (frame names swap a b).value freshKey := by
  refine ⟨by change 40 ∉ names.restricted; decide, ?_⟩
  intro r _ he
  change 2 ≤ r.nodeCount
  by_contra hsmall
  rcases Term.nodeCount_one_cases (by omega : r.nodeCount ≤ 1) with
    ⟨x, rfl⟩ | ⟨v, rfl⟩ | ⟨c, rfl⟩
  · obtain ⟨_, hshape, _⟩ := he.pk_irreducible_shape (name_irreducible x)
    cases hshape
  · have hv := frame_projection_pk_origin names swap a b v .handle he.symm
    have hi : v = 0 := Term.var.inj hv
    subst v
    have hn := (EqE.name_iff 40 10).mp ((EqE.pk_iff _ _).mp he)
    omega
  · obtain ⟨_, hshape, _⟩ := he.pk_irreducible_shape (constant_irreducible c)
    cases hshape

/-- Dropping minimum size admits a projection wrapper outside the classified
syntax. The smaller public handle has exactly the same value. -/
theorem minimum_origin_needs_minimum (swap : Bool) :
    wrapper.Public names.restricted ∧ EqE ((world swap).eval wrapper) (publicKey names) ∧
    ¬ PublicKeyRecipeForm wrapper ∧ ¬ MinimalRecipe names.restricted (world swap).value wrapper := by
  have he : EqE ((world swap).eval wrapper) ((world swap).eval handle) := (RootStep.fst _ _).sound
  refine ⟨by trivial, he, ?_, ?_⟩
  · rintro (h | ⟨a, h⟩) <;> cases h
  · intro hm
    exact hm.no_smaller (s := handle) trivial he (by decide)

/-- The general public-constructor separation uses the full secret-name policy.
A nonce-only policy permits the literal secret-key argument. This recipe is not
claimed to be minimum, since the published handle is smaller. -/
theorem full_secret_policy_required :
    (Term.unary .pk (.name 10) : Recipe 3).Public names.nonceNames ∧
    ¬ (Term.unary .pk (.name 10) : Recipe 3).Public names.restricted ∧
    ∀ swap : Bool, EqE ((world swap).eval (.unary .pk (.name 10))) ((world swap).eval handle) := by
  refine ⟨?_, ?_, fun _ => .refl _⟩
  · change 10 ∉ names.nonceNames
    decide
  · change ¬ (10 ∉ names.restricted)
    decide

abbrev target : Ground := .unary .pk (.name 40)
abbrev delayedPair : Ground := .unary .fst (.binary .pair (.binary .pair target (.const .bottom)) (.const .one))
abbrev delayedKey : Ground := .unary .fst (.binary .pair (.name 50) (.const .bottom))
abbrev ciphertext : Ground := .ternary .penc (.unary .pk (.name 50)) (.name 60) target
abbrev delayedPartial : Ground := .unary .fst
  (.binary .pair (.binary .partialDecrypt (.name 50) ciphertext) (.const .bottom))

/-- The new path inversions cover a delayed pair, a delayed E5 key and a delayed
E6 partial-decryption value; target key output is independently fixed. -/
theorem delayed_key_output_paths :
    EqE (.unary .fst delayedPair) target ∧
    (∃ x y : Ground, ReducesModulo delayedPair (.binary .pair x y) ∧ EqE x target) ∧
    EqE (.binary .dec delayedKey ciphertext) target ∧
    (∃ p : Ground, DecryptionMatch delayedKey ciphertext p ∧ EqE p target) ∧
    EqE (.binary .dec delayedPartial ciphertext) target ∧
    (∃ p : Ground, DecryptionMatch delayedPartial ciphertext p ∧ EqE p target) := by
  have hp : EqE (.unary .fst delayedPair) target :=
    (EqE.unary .fst (RootStep.fst _ _).sound).trans (RootStep.fst _ _).sound
  have hd : EqE (.binary .dec delayedKey ciphertext) target :=
    (EqE.binary .dec (RootStep.fst _ _).sound (.refl _)).trans (RootStep.decrypt _ _ _).sound
  have hs : EqE (.binary .dec delayedPartial ciphertext) target :=
    (EqE.binary .dec (RootStep.fst _ _).sound (.refl _)).trans (RootStep.partial_decrypt _ _ _).sound
  exact ⟨hp, hp.projection_pk_inversion (Or.inl rfl), hd, hd.decryption_pk_inversion,
    hs, hs.decryption_pk_inversion⟩

/-- A ciphertext field contains a public-key argument, but another tuple
projection cannot expose that constructor argument as a public key. -/
theorem ballot_field_projection_is_not_key (swap : Bool) :
    ¬ EqE ((world swap).eval (.unary .fst ((Term.var 1).project 0))) (publicKey names) :=
  voter_projection_not_pk names swap left right 0
    (.step .fst (Or.inl rfl) (.project 1 0)) _

/-- Key construction respects reduction in its argument and still distinguishes
independent fresh public names. -/
theorem reducible_key_argument_and_distinct_keys (swap : Bool) :
    EqE ((world swap).eval (.unary .pk (.unary .fst (.binary .pair (.name 40) (.const .bottom)))))
      ((world swap).eval freshKey) ∧
    ¬ EqE ((world swap).eval freshKey) ((world swap).eval (.unary .pk (.name 41))) := by
  refine ⟨.unary .pk (RootStep.fst _ _).sound, ?_⟩
  intro he
  have hn := (EqE.name_iff 40 41).mp ((EqE.pk_iff _ _).mp he)
  omega

/-- The full minimum-key induction interface is inhabited with one- and two-node
minima and unequal key values. Identical candidate assignments discharge the
bounded premise without assuming different-vote static equivalence. -/
theorem minimum_key_step_inhabited :
    MinimalRecipe names.restricted (frame names false left left).value freshKey ∧
    MinimalRecipe names.restricted (frame names false left left).value handle ∧
    freshKey.nodeCount + handle.nodeCount = 3 ∧
    ¬ EqE ((frame names false left left).eval freshKey) ((frame names false left left).eval handle) ∧
    (EqE ((frame names false left left).eval freshKey) ((frame names false left left).eval handle) ↔
      EqE ((frame names true left left).eval freshKey) ((frame names true left left).eval handle)) := by
  have hf := constructed_key_minimum false left left
  have hh : MinimalRecipe names.restricted (frame names false left left).value handle :=
    MinimalRecipe.of_nodeCount_one trivial rfl
  refine ⟨hf, hh, rfl, ?_, minimum_public_key_equality_swap names left left freshKey handle hf hh
    (k := .name 40) (l := .name 10) (.refl _) (.refl _) (CiphertextObservationSPOT.diagonal_observations _)⟩
  exact constructed_key_not_election_key names false left left (.name 40) hf.isPublic

end ExplainableCrypto.Helios.Symbolic.PublicKeyObservationSPOT
