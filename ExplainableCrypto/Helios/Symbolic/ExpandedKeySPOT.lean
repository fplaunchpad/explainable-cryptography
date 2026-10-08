import ExplainableCrypto.Helios.Symbolic.ExpandedPublicKeyTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedOriginSPOT

namespace ExplainableCrypto.Helios.Symbolic.ExpandedKeySPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []

private theorem numeric (swap : Bool) : ExpandedResultsNumeric names swap left right [] :=
  accepted_expanded_results_numeric names HistoricalFrameSPOT.fixture_names_fresh left right [] (by simp) trivial swap

/-- The retained key is a minimum public recipe and the unique minimum recipe
for its value. The statement is inhabited in each actual swapped world. -/
theorem election_handle_is_unique_minimum (swap : Bool) :
    MinimalRecipe names.restricted (world swap).value (.var (expandedOld 0)) ∧
    ∀ r, MinimalRecipe names.restricted (world swap).value r →
      EqE ((world swap).eval r) (publicKey names) → r = .var (expandedOld 0) :=
  ⟨.of_nodeCount_one trivial rfl,
    fun r hm he => expanded_minimum_election_key_handle names swap left right [] (by simp) (numeric swap) r hm he⟩

/-- A published partial can be used as a new public key's argument. It gives a
minimum size-two constructor, distinct from the retained election key. -/
theorem partial_argument_key_is_minimum (swap : Bool) :
    let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
    MinimalRecipe names.restricted (world swap).value (.unary .pk a) ∧
    ¬ EqE ((world swap).eval (.unary .pk a)) (publicKey names) :=
  ⟨expanded_minimum_pk_of_child names swap left right [] (by simp) (numeric swap)
      (.var (expandedPartial 0)) (.of_nodeCount_one trivial rfl),
    expanded_constructed_key_not_election_key names swap left right [] (by simp) (.var (expandedPartial 0)) trivial⟩

/-- Constructor closure also supports nested partial/result arguments. -/
theorem nested_partial_argument_key_is_minimum (swap : Bool) :
    let a : Recipe (ExpandedHandles 1) := .binary .partialDecrypt (.var (expandedPartial 0)) (.var (expandedResult 1))
    MinimalRecipe names.restricted (world swap).value (.unary .pk a) ∧
    ¬ EqE ((world swap).eval (.unary .pk a)) (publicKey names) :=
  ⟨expanded_minimum_pk_of_child names swap left right [] (by simp) (numeric swap) _
      (expanded_minimum_partial_of_children names swap left right [] (by simp) (numeric swap)
        (.var (expandedPartial 0)) (.var (expandedResult 1))
        (.of_nodeCount_one trivial rfl) (.of_nodeCount_one trivial rfl)),
    expanded_constructed_key_not_election_key names swap left right [] (by simp)
      (.binary .partialDecrypt (.var (expandedPartial 0)) (.var (expandedResult 1))) ⟨trivial,trivial⟩⟩

/-- A public projection wrapper has election-key value but fails both the
minimum premise and the proposed raw key syntax. -/
theorem projection_wrapper_requires_minimum (swap : Bool) :
    let r : Recipe (ExpandedHandles 1) := .unary .fst (.binary .pair (.var (expandedOld 0)) (.name 90))
    EqE ((world swap).eval r) (publicKey names) ∧
    ¬ MinimalRecipe names.restricted (world swap).value r ∧ ¬ ExpandedPublicKeyRecipeForm r := by
  let r : Recipe (ExpandedHandles 1) := .unary .fst (.binary .pair (.var (expandedOld 0)) (.name 90))
  have he : EqE ((world swap).eval r) (publicKey names) := .equation (.fst _ _)
  refine ⟨he,?_,?_⟩
  · intro hm
    have h := expanded_minimum_election_key_handle names swap left right [] (by simp) (numeric swap) r hm he
    unfold r at h
    cases h
  · rintro (h | ⟨a,h⟩) <;> cases h

/-- Removing the election secret from the name policy makes a constructed key
alias the handle. Its public size-one argument no longer gives a minimum key. -/
theorem secret_restriction_is_required (swap : Bool) :
    let a : Recipe (ExpandedHandles 1) := .name names.secretKey
    a.Public names.nonceNames ∧ ¬ a.Public names.restricted ∧
    EqE ((world swap).eval (.unary .pk a)) (publicKey names) ∧
    MinimalRecipe names.nonceNames (world swap).value a ∧
    ¬ MinimalRecipe names.nonceNames (world swap).value (.unary .pk a) := by
  have hp : (Term.name names.secretKey : Recipe (ExpandedHandles 1)).Public names.nonceNames := by
    change names.secretKey ∉ names.nonceNames
    decide
  refine ⟨hp,by change ¬ names.secretKey ∉ names.restricted; decide,.refl _,.of_nodeCount_one hp rfl,?_⟩
  intro hm
  have h := hm.least (.var (expandedOld 0)) trivial (.refl _)
  change 2 ≤ 1 at h
  omega

/-- A projection from either kind of new handle cannot yield any public key.
This checks selectors rather than restricting the new values to bare atoms. -/
theorem new_handle_projection_not_key (swap : Bool) (j : Fin 2) (key : Ground) :
    ¬ EqE ((world swap).eval (.unary .fst (.var (expandedPartial j)))) (.unary .pk key) ∧
    ¬ EqE ((world swap).eval (.unary .fst (.var (expandedResult j)))) (.unary .pk key) := by
  constructor
  · intro he
    have h := expanded_projection_pk_origin names swap left right [] (numeric swap) (expandedPartial j)
      (.step .fst (by trivial) .handle) he
    cases h
  · intro he
    have h := expanded_projection_pk_origin names swap left right [] (numeric swap) (expandedResult j)
      (.step .fst (by trivial) .handle) he
    cases h

/-- The accepted-election equality interface is inhabited for distinct
constructed keys. The diagonal election supplies its smaller-test premise. -/
theorem constructed_key_equality_nonconstant :
    let φ := expandedFrame names false left left []
    let ψ := expandedFrame names true left left []
    let r : Recipe (ExpandedHandles 1) := .unary .pk (.name 40)
    let s : Recipe (ExpandedHandles 1) := .unary .pk (.name 41)
    (EqE (φ.eval r) (φ.eval s) ↔ EqE (ψ.eval r) (ψ.eval s)) ∧ ¬ EqE (φ.eval r) (φ.eval s) := by
  have hn := accepted_expanded_results_numeric names HistoricalFrameSPOT.fixture_names_fresh left left [] (by simp) trivial false
  have h40 : (Term.name 40 : Recipe (ExpandedHandles 1)).Public names.restricted := by change 40 ∉ names.restricted; decide
  have h41 : (Term.name 41 : Recipe (ExpandedHandles 1)).Public names.restricted := by change 41 ∉ names.restricted; decide
  refine ⟨accepted_expanded_minimum_public_key_equality_swap names HistoricalFrameSPOT.fixture_names_fresh
    left left [] (by simp) trivial (.unary .pk (.name 40)) (.unary .pk (.name 41))
    (expanded_minimum_pk_of_child names false left left [] (by simp) hn _ (.of_nodeCount_one h40 rfl))
    (expanded_minimum_pk_of_child names false left left [] (by simp) hn _ (.of_nodeCount_one h41 rfl))
    (.refl _) (.refl _) (fun _ _ _ _ _ => Iff.rfl),?_⟩
  intro he
  exact absurd ((EqE.name_iff 40 41).mp ((EqE.pk_iff _ _).mp he)) (by decide)

/-- Structured-key E5 still succeeds with a key-valued payload. Its decryption
wrapper is nonminimum, so key origins do not silently disable decryption. -/
theorem successful_decryption_returns_key (swap : Bool) :
    let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
    let b := keyCiphertext a (.name 60) (.unary .pk (.name 90))
    EqE ((world swap).eval (.binary .dec a b)) (.unary .pk (.name 90)) ∧
    ¬ MinimalRecipe names.restricted (world swap).value (.binary .dec a b) ∧
    ¬ ExpandedPublicKeyRecipeForm (.binary .dec a b) := by
  let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
  let b := keyCiphertext a (.name 60) (.unary .pk (.name 90))
  have hd : DecryptionMatch ((world swap).eval a) ((world swap).eval b) (.unary .pk (.name 90)) :=
    ⟨_,.name 60,Or.inl (.refl _),.refl _⟩
  refine ⟨hd.reduces.sound,?_,?_⟩
  · intro hm
    exact accepted_expanded_minimum_decryption_no_match names HistoricalFrameSPOT.fixture_names_fresh
      left right [] (by simp) trivial swap a b hm _ hd
  · rintro (h | ⟨c,h⟩) <;> cases h

end ExplainableCrypto.Helios.Symbolic.ExpandedKeySPOT
