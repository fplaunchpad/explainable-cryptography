import ExplainableCrypto.Helios.Symbolic.ExpandedGroupEquality
import ExplainableCrypto.Helios.Symbolic.ExpandedMulSPOT
import ExplainableCrypto.Helios.Symbolic.ExpandedGroupExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedGroupSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []
abbrev trustee : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
abbrev honest : Combination (HonestIndex 1) := .leaf (0,0)
abbrev twice : Combination (HonestIndex 1) := .mul honest honest

private theorem nonce_mem (i : HonestIndex 1) : names.nonce i.1 i.2 ∈ names.restricted :=
  Finset.mem_union_right _ (names.nonce_mem_nonceNames i.1 i.2)
private theorem protectedFrame (swap : Bool) : (world swap).OpaqueProtected :=
  expanded_frame_opaque_protected names swap left right [] (by simp)

/-- The real trustee slot is opaque-protected but fails the old raw nonce-safe
predicate. Treating these protection conditions as interchangeable is false. -/
theorem actual_partial_needs_opaque_protection (swap : Bool) :
    OpaqueProtectedValue names.restricted ((world swap).eval trustee) ∧
    ¬ (((world swap).eval trustee).nonceSafe names.restricted = true) := by
  refine ⟨(protectedFrame swap).eval trustee trivial,?_⟩
  cases swap <;> decide

/-- Mixed nonce cancellation applies to an actual partial and a reducible
public delayed, retaining exact honest occurrence bags and remainder equality. -/
theorem partial_alias_mixed_nonce (swap : Bool) :
    let delayed : Recipe (ExpandedHandles 1) := .unary .fst (.binary .pair trustee (.name 40))
    EqE (.binary .compose ((world swap).eval trustee) (combinationNonce names honest))
      (.binary .compose ((world swap).eval delayed) (combinationNonce names honest)) := by
  apply (opaque_mixed_named_nonce_eq_iff (fun i : HonestIndex 1 => names.nonce i.1 i.2)
    HistoricalFrameSPOT.fixture_names_fresh.2.1 nonce_mem honest honest _ _
    ((protectedFrame swap).eval trustee trivial) ((protectedFrame swap).eval (.unary .fst (.binary .pair trustee (.name 40))) ⟨trivial,by change 40 ∉ names.restricted; decide⟩)).mpr
  exact ⟨rfl,(EqE.equation (.fst _ _)).symm⟩

/-- An actual public partial cannot compensate for deleting a repeated honest
nonce occurrence, even though all copies have the same nonce value. -/
theorem duplicate_honest_nonce_retained (swap : Bool) :
    ¬ EqE (.binary .compose ((world swap).eval trustee) (combinationNonce names honest))
      (.binary .compose ((world swap).eval trustee) (combinationNonce names twice)) := by
  intro he
  have h := (opaque_mixed_named_nonce_eq_iff (fun i : HonestIndex 1 => names.nonce i.1 i.2)
    HistoricalFrameSPOT.fixture_names_fresh.2.1 nonce_mem honest twice _ _
    ((protectedFrame swap).eval trustee trivial) ((protectedFrame swap).eval trustee trivial)).mp he
  have hc := congrArg Multiset.card h.1
  change 1 = 2 at hc
  omega

/-- A present opaque public nonce contribution cannot disappear into a purely
honest group. No global composition unit is assumed. -/
theorem mixed_partial_not_honest (swap : Bool) :
    ¬ EqE (.binary .compose ((world swap).eval trustee) (combinationNonce names honest))
      (combinationNonce names twice) :=
  opaque_mixed_nonce_not_honest _ nonce_mem honest twice _ ((protectedFrame swap).eval trustee trivial)

/-- All cross-class comparisons of actual public groups are rejected; their
reverse directions follow by symmetry of ciphertext equality. -/
theorem cross_group_classes_rejected (swap : Bool) :
    let a : CiphertextGroup 1 (ExpandedHandles 1) := .constructed trustee (.const .zero)
    let b : CiphertextGroup 1 (ExpandedHandles 1) := .honest honest
    let c : CiphertextGroup 1 (ExpandedHandles 1) := .mixed trustee (.const .zero) honest
    let value := fun g : CiphertextGroup 1 (ExpandedHandles 1) =>
      Term.ternary .penc (.name 40) (g.nonce names (world swap)) (g.message (world swap) swap left right)
    ¬ EqE (value a) (value b) ∧ ¬ EqE (value a) (value c) ∧ ¬ EqE (value b) (value c) := by
  have classify := expanded_group_ciphertext_eq_iff names HistoricalFrameSPOT.fixture_names_fresh swap left right [] (by simp)
  refine ⟨?_,?_,?_⟩
  · intro he
    exact (classify (.constructed trustee (.const .zero)) (.honest honest) ⟨trivial,trivial⟩ trivial _ _).mp he |>.2
  · intro he
    exact (classify (.constructed trustee (.const .zero)) (.mixed trustee (.const .zero) honest)
      ⟨trivial,trivial⟩ ⟨trivial,trivial⟩ _ _).mp he |>.2
  · intro he
    exact (classify (.honest honest) (.mixed trustee (.const .zero) honest) trivial ⟨trivial,trivial⟩ _ _).mp he |>.2

/-- Mixed payloads can become equal after adding their honest numeric part
although their unpadded public payloads differ. Present zero is load-bearing. -/
theorem mixed_payload_requires_padding (swap : Bool) :
    let a : CiphertextGroup 1 (ExpandedHandles 1) := .mixed trustee (.name 40) honest
    let b : CiphertextGroup 1 (ExpandedHandles 1) := .mixed trustee (.binary .add (.name 40) (.const .zero)) honest
    EqE (.ternary .penc (.name 50) (a.nonce names (world swap)) (a.message (world swap) swap left right))
      (.ternary .penc (.name 50) (b.nonce names (world swap)) (b.message (world swap) swap left right)) ∧
    ¬ EqE ((world swap).eval (.name 40)) ((world swap).eval (.binary .add (.name 40) (.const .zero))) := by
  have hp : (Term.name (V := Fin (ExpandedHandles 1)) 40).Public names.restricted := by change 40 ∉ names.restricted; decide
  refine ⟨?_,fun he => arithmetic_not_eqE_name .add (Or.inl rfl) _ _ 40 he.symm⟩
  apply (expanded_group_ciphertext_eq_iff names HistoricalFrameSPOT.fixture_names_fresh swap left right [] (by simp)
    (.mixed trustee (.name 40) honest) (.mixed trustee (.binary .add (.name 40) (.const .zero)) honest)
    ⟨trivial,hp⟩ ⟨trivial,hp,trivial⟩ _ _).mpr
  refine ⟨.refl _,rfl,.refl _,?_⟩
  exact (baseEq_of_addSyntaxSummary_eq (by simp only [Frame.eval,Term.subst]; decide)).sound

/-- Group equality does not erase the public key comparison. Identical grouped
components with different literal keys still give unequal ciphertexts. -/
theorem key_equality_remains_required (swap : Bool) :
    let a : CiphertextGroup 1 (ExpandedHandles 1) := .constructed trustee (.var (expandedResult 0))
    ¬ EqE (.ternary .penc (.name 40) (a.nonce names (world swap)) (a.message (world swap) swap left right))
      (.ternary .penc (.name 41) (a.nonce names (world swap)) (a.message (world swap) swap left right)) := by
  dsimp only
  intro he
  have hk := ((EqE.penc_iff _ _ _ _ _ _).mp he).1
  have h := (EqE.name_iff 40 41).mp hk
  omega

/-- Protection may hold through an E-equal safe representative even when the
supplied raw term contains an unobservable restricted name. -/
theorem raw_unsafe_remainder_is_allowed :
    let r : Ground := .unary .fst (.binary .pair (.name 40) (.name names.secretKey))
    ¬ (r.opaqueSafe names.restricted = true) ∧ OpaqueProtectedValue names.restricted r ∧
    EqE (.binary .compose r (combinationNonce names honest))
      (.binary .compose (.name 40) (combinationNonce names honest)) := by
  let r : Ground := .unary .fst (.binary .pair (.name 40) (.name names.secretKey))
  have hs : (Term.name (V := Empty) 40).opaqueSafe names.restricted = true := by decide
  have hr : OpaqueProtectedValue names.restricted r := ⟨.name 40,.equation (.fst _ _),hs⟩
  refine ⟨by decide,hr,?_⟩
  exact (opaque_mixed_named_nonce_eq_iff (fun i : HonestIndex 1 => names.nonce i.1 i.2)
    HistoricalFrameSPOT.fixture_names_fresh.2.1 nonce_mem honest honest r (.name 40) hr
    ⟨.name 40,.refl _,hs⟩).mpr ⟨rfl,.equation (.fst _ _)⟩

/-- Existing merge laws now apply at the expanded handle count for every pair
of group classes, preserving publicness, components and the original bounds. -/
theorem expanded_merge_laws (swap : Bool) (a b : CiphertextGroup 1 (ExpandedHandles 1))
    (ha : a.Public names.restricted) (hb : b.Public names.restricted) :
    (a.merge b).Public names.restricted ∧ (a.merge b).budget ≤ a.budget+b.budget+1 ∧
    BaseEq (.binary .compose (a.nonce names (world swap)) (b.nonce names (world swap)))
      ((a.merge b).nonce names (world swap)) ∧
    BaseEq (.binary .add (a.message (world swap) swap left right) (b.message (world swap) swap left right))
      ((a.merge b).message (world swap) swap left right) :=
  ⟨CiphertextGroup.merge_public a b ha hb,CiphertextGroup.merge_budget a b,
    CiphertextGroup.merge_nonce names _ a b,CiphertextGroup.merge_message _ swap left right a b⟩

/-- The transfer theorem includes zero-padded mixed payload comparisons. A
diagonal election inhabits its explicit smaller-group-observation premise. -/
theorem bounded_mixed_component_transfer :
    let φ := expandedFrame names false left left []
    let ψ := expandedFrame names true left left []
    let a : CiphertextGroup 1 (ExpandedHandles 1) := .mixed trustee (.var (expandedResult 0)) honest
    let b : CiphertextGroup 1 (ExpandedHandles 1) := .mixed trustee (.const .zero) honest
    (EqE (a.nonce names φ) (b.nonce names φ) ∧ EqE (a.message φ false left left) (b.message φ false left left)) ↔
    (EqE (a.nonce names ψ) (b.nonce names ψ) ∧ EqE (a.message ψ true left left) (b.message ψ true left left)) :=
  expanded_group_components_equality_swap names HistoricalFrameSPOT.fixture_names_fresh false true left left []
    (by simp) _ _ ⟨trivial,trivial⟩ ⟨trivial,trivial⟩ (fun _ _ _ _ _ => Iff.rfl)

end ExplainableCrypto.Helios.Symbolic.ExpandedGroupSPOT
