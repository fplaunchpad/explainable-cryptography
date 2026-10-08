import ExplainableCrypto.Helios.Symbolic.SuccessfulDecryptionClosure
import ExplainableCrypto.Helios.Symbolic.SuccessfulCheckSPOT

namespace ExplainableCrypto.Helios.Symbolic.SuccessfulDecryptionSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world := LocalRootSPOT.world
abbrev secret := LocalRootSPOT.partialRecipe
abbrev key := LocalRootSPOT.key
abbrev cipher : Recipe 3 := .ternary .penc key (.name 40) (.var 2)
abbrev direct : Recipe 3 := .binary .dec secret cipher
abbrev partialKey : Recipe 3 := .binary .partialDecrypt secret cipher
abbrev partialRecipe : Recipe 3 := .binary .dec partialKey cipher

private theorem cipher_minimum (swap : Bool) : MinimalRecipe names.restricted (world swap).value cipher :=
  minimum_penc_of_children names swap left right _ _ _
    (LocalRootSPOT.nested_constructor_minima swap).2.1
    (.of_nodeCount_one (by change 40 ∉ names.restricted; decide) rfl) (.of_nodeCount_one trivial rfl)

private theorem initial : Frame.StaticEq (world false) (world true) :=
  initial_frame_staticEq names HistoricalFrameSPOT.fixture_names_fresh left right

private theorem below (bound : Nat) : Frame.ObservationsBelow (world false) (world true) bound := by
  intro r s hr hs _
  exact initial r s hr hs

/-- The three-node partial-decryption term is also a legal E5 secret key.
The eleven-node decrypt returns the public ballot handle, not a constant. -/
theorem structured_direct_decryption :
    Frame.MinimumChildren (world false) direct ∧ direct.nodeCount=11 ∧
    EqE ((world false).eval direct) ((world false).eval (.var 2)) ∧
    EqE ((world true).eval direct) ((world true).eval (.var 2)) ∧
    Frame.SharedMinimum (world false) (world true) direct := by
  have ha := (LocalRootSPOT.nested_constructor_minima false).1
  have hm : ∃ m, DecryptionMatch ((world false).eval secret) ((world false).eval cipher) m :=
    ⟨(world false).eval (.var 2),(world false).eval secret,.name 40,Or.inl (.refl _),.refl _⟩
  have he := minimum_key_constructed_decryption_transfer names false true left right secret key
    (.name 40) (.var 2) ha (cipher_minimum false).isPublic (below _) hm
  exact ⟨⟨ha,cipher_minimum false⟩,rfl,(RootStep.decrypt _ _ _).sound,he,
    ⟨.var 2,.of_nodeCount_one trivial rfl,(RootStep.decrypt _ _ _).sound,he⟩⟩

/-- E6 binds the complete seven-node ciphertext. Both minimum children enter
the full local theorem and share the actual one-node payload recipe. -/
theorem bound_partial_decryption :
    Frame.MinimumChildren (world false) partialRecipe ∧ partialRecipe.nodeCount=19 ∧
    EqE ((world false).eval partialRecipe) ((world false).eval (.var 2)) ∧
    EqE ((world true).eval partialRecipe) ((world true).eval (.var 2)) ∧
    Frame.SharedMinimum (world false) (world true) partialRecipe := by
  have ha := minimum_partial_of_children names false left right _ _
    (LocalRootSPOT.nested_constructor_minima false).1 (cipher_minimum false)
  have hc : Frame.MinimumChildren (world false) partialRecipe := ⟨ha,cipher_minimum false⟩
  have hf : Frame.SharedMinimaBelow (world false) (world true) partialRecipe.nodeCount :=
    fun r hp _ => initial.common_minima r hp
  have hr : Frame.SharedMinimaBelow (world true) (world false) partialRecipe.nodeCount :=
    fun r hp _ => initial.symm.common_minima r hp
  exact ⟨hc,rfl,(RootStep.partial_decrypt _ _ _).sound,(RootStep.partial_decrypt _ _ _).sound,
    minimum_children_decryption_shared_of_two_way_minima names HistoricalFrameSPOT.fixture_names_fresh
      false true left right _ _ hc.1 hc.2 hf hr⟩

/-- Different actual ballots remain statically equivalent. Distinct public
names remain distinguishable, excluding pointwise-identical or collapsed worlds. -/
theorem nonliteral_initial_equivalence :
    Frame.StaticEq (world false) (world true) ∧
    (world false).eval (.var 2) ≠ (world true).eval (.var 2) ∧
    ¬ EqE ((world true).eval (.name 40)) ((world true).eval (.name 41)) := by
  refine ⟨initial,by decide,?_⟩
  intro he
  have h := (EqE.name_iff 40 41).mp he
  omega

/-- The smallest candidate count retains abstention, a selected vote and
component/aggregate aliasing under the full unbounded equality theorem. -/
theorem one_candidate_initial_equivalence :
    Frame.StaticEq (ProofObservationSPOT.oneWorld false) (ProofObservationSPOT.oneWorld true) ∧
    EqE ((ProofObservationSPOT.oneWorld true).eval ((Term.var 1).project 1))
      ((ProofObservationSPOT.oneWorld true).eval ((Term.var 1).project 2)) :=
  ⟨initial_frame_staticEq ProofObservationSPOT.oneNames NumericReflectionSPOT.fixture_names_fresh
    ProofObservationSPOT.oneLeft ProofObservationSPOT.oneRight,
    (ProofObservationSPOT.one_candidate_fields_coincide true).2⟩

abbrev loose (swap : Bool) : Frame ProofObservationSPOT.oneNames.nonceNames 3 :=
  ⟨(ProofObservationSPOT.oneWorld swap).value⟩
abbrev leak : Recipe 3 := .binary .dec (.name ProofObservationSPOT.oneNames.secretKey)
  ((Term.var 1).project 0)

/-- Exposing the election secret gives an actual distinguisher: the same
recipe returns zero before the swap and one afterwards. Full restriction is
therefore load-bearing in initial static equivalence. -/
theorem full_secret_restriction_required :
    leak.Public ProofObservationSPOT.oneNames.nonceNames ∧
    ¬ leak.Public ProofObservationSPOT.oneNames.restricted ∧
    EqE ((loose false).eval leak) (.const .zero) ∧
    EqE ((loose true).eval leak) (.const .one) ∧
    ¬ Frame.StaticEq (loose false) (loose true) := by
  have hz : EqE ((loose false).eval leak) (.const .zero) :=
    (normalizeRaw_reachable _).to_modulo.sound
  have ho : EqE ((loose true).eval leak) (.const .one) :=
    (normalizeRaw_reachable _).to_modulo.sound
  have hp : leak.Public ProofObservationSPOT.oneNames.nonceNames := by
    simp only [Term.Public,Term.project,Term.drop]; decide
  refine ⟨hp,?_,hz,ho,?_⟩
  · simp only [Term.Public,Term.project,Term.drop]; decide
  · intro hs
    exact zero_not_one (((hs leak (.const .zero) hp trivial).mp hz).symm.trans ho)

/-- A wrapper around a constructed ciphertext still decrypts, but it is not
itself a minimum or a raw penc. The right-child minimum premise is necessary
for the syntax conclusion in successful-ciphertext classification. -/
theorem minimum_ciphertext_premise_required :
    let b := SuccessfulCheckSPOT.wrap cipher
    EqE ((world false).eval (.binary .dec secret b)) ((world false).eval (.var 2)) ∧
    ¬ MinimalRecipe names.restricted (world false).value b ∧
    ¬ (∃ k r p, b = .ternary .penc k r p) := by
  dsimp only
  refine ⟨(EqE.binary .dec (.refl _) (RootStep.fst _ _).sound).trans
    (RootStep.decrypt _ _ _).sound,?_,?_⟩
  · intro hm
    exact hm.no_smaller (cipher_minimum false).isPublic (RootStep.fst _ _).sound (by decide)
  · rintro ⟨k,r,p,h⟩
    cases h

/-- The gate's binding defect has a real source-only match in published
frames, detected by a smaller public ciphertext equality. -/
theorem wrong_binding_blocks_decryption :
    ¬ (∃ m, DecryptionMatch ((DecryptionProbeSPOT.probeFrame false).eval (.binary .partialDecrypt (.var 0) (.var 1)))
      ((DecryptionProbeSPOT.probeFrame false).eval (.var 2)) m) ∧
    (∃ m, DecryptionMatch ((DecryptionProbeSPOT.probeFrame true).eval (.binary .partialDecrypt (.var 0) (.var 1)))
      ((DecryptionProbeSPOT.probeFrame true).eval (.var 2)) m) ∧
    ¬ (DecryptionProbeSPOT.probeFrame false).ObservationsBelow (DecryptionProbeSPOT.probeFrame true) 6 :=
  DecryptionProbeSPOT.binding_probe_detects_new_match

/-- A literal wrong secret cannot decrypt the public name-90 ciphertext. -/
theorem wrong_key_blocks_decryption :
    ¬ (∃ m, DecryptionMatch (.name 41 : Ground) (DecryptionProbeSPOT.cipher 50) m) := by
  rintro ⟨m,k,r,hk,hc⟩
  have hkey := (EqE.pk_iff _ _).mp ((EqE.penc_iff _ _ _ _ _ _).mp hc.sound).1
  rcases hk with hd | hp
  · have h := (EqE.name_iff 41 40).mp (hd.sound.trans hkey.symm)
    omega
  · have h := ((name_irreducible 41).reducesModulo hp).head_eq
    cases h

end ExplainableCrypto.Helios.Symbolic.SuccessfulDecryptionSPOT
