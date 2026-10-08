import ExplainableCrypto.Helios.Symbolic.PartialDecryptionObservationInduction
import ExplainableCrypto.Helios.Symbolic.PublicKeyObservationSPOT

namespace ExplainableCrypto.Helios.Symbolic.PartialDecryptionObservationSPOT
open Historical General
abbrev names := PublicKeyObservationSPOT.names
abbrev left := PublicKeyObservationSPOT.left
abbrev right := PublicKeyObservationSPOT.right
abbrev world := PublicKeyObservationSPOT.world
abbrev literal : Recipe 3 := .binary .partialDecrypt (.name 40) (.name 50)
abbrev reversed : Recipe 3 := .binary .partialDecrypt (.name 50) (.name 40)
abbrev wrapper : Recipe 3 := .unary .fst (.binary .pair literal (.const .bottom))
abbrev target : Ground := .binary .partialDecrypt (.name 40) (.name 50)

/-- Every public literal pair of names attains the exact three-node minimum in
an initial frame. The lower bound excludes all smaller recipes and handles. -/
theorem literal_partial_minimum (swap : Bool) (a b : CandidateSubstitution 1 Empty)
    (x y : Nat) (hx : x ∉ names.restricted) (hy : y ∉ names.restricted) :
    MinimalRecipe names.restricted (frame names swap a b).value
      (.binary .partialDecrypt (.name x) (.name y)) := by
  have hp : (Term.binary .partialDecrypt (.name x) (.name y) : Recipe 3).Public names.restricted := ⟨hx, hy⟩
  obtain ⟨m, hm, he⟩ := exists_minimal_recipe (σ := (frame names swap a b).value) _ hp
  obtain ⟨u, v, rfl⟩ := minimum_partial_decryption_form names swap a b names.restricted m hm he.symm
  refine ⟨hp, fun s hs hes => ?_⟩
  have hle := hm.least s hs (he.symm.trans hes)
  have hu := u.nodeCount_pos
  have hv := v.nodeCount_pos
  simp only [Term.nodeCount] at hle ⊢
  omega

/-- The omitted-minimum mutation has a public counterexample with a smaller
constructor of the same value; it cannot pass by rejecting every constructor. -/
theorem minimum_origin_needs_minimum (swap : Bool) :
    wrapper.Public names.restricted ∧ EqE ((world swap).eval wrapper) target ∧
    ¬ (∃ a b, wrapper = .binary .partialDecrypt a b) ∧
    ¬ MinimalRecipe names.restricted (world swap).value wrapper := by
  have hp : literal.Public names.restricted := by change 40 ∉ names.restricted ∧ 50 ∉ names.restricted; decide
  have he : EqE ((world swap).eval wrapper) ((world swap).eval literal) := (RootStep.fst _ _).sound
  refine ⟨⟨hp, trivial⟩, he, ?_, ?_⟩
  · rintro ⟨a, b, h⟩
    cases h
  · intro hm
    exact hm.no_smaller hp he (by decide)

/-- Both constructor fields may reduce, but their order is observable. Literal
40 and 50 are independent expected endpoints, not normalizer output. -/
theorem reducible_arguments_and_order (swap : Bool) :
    EqE ((world swap).eval (.binary .partialDecrypt
      (.unary .fst (.binary .pair (.name 40) (.const .bottom)))
      (.unary .fst (.binary .pair (.name 50) (.const .bottom))))) target ∧
    ¬ EqE ((world swap).eval literal) ((world swap).eval reversed) := by
  refine ⟨.binary .partialDecrypt (RootStep.fst _ _).sound (RootStep.fst _ _).sound, ?_⟩
  intro he
  have hn := (EqE.name_iff 40 50).mp ((EqE.partialDecrypt_iff _ _ _ _).mp he).1
  omega

abbrev c0 : Ground := .ternary .penc (.unary .pk (.name 50)) (.name 60) (.const .zero)
abbrev c1 : Ground := .ternary .penc (.unary .pk (.name 50)) (.name 61) (.const .zero)

/-- E6 succeeds on a matching complete ciphertext; same key and plaintext with
a changed nonce still give a distinct partial-decryption constructor value. -/
theorem complete_ciphertext_binding :
    EqE (.binary .dec (.binary .partialDecrypt (.name 50) c0) c0) (.const .zero) ∧
    ¬ EqE (.binary .partialDecrypt (.name 50) c0) (.binary .partialDecrypt (.name 50) c1) := by
  refine ⟨(RootStep.partial_decrypt _ _ _).sound, ?_⟩
  intro he
  have hc := ((EqE.partialDecrypt_iff _ _ _ _).mp he).2
  have hn := (EqE.name_iff 60 61).mp ((EqE.penc_iff _ _ _ _ _ _).mp hc).2.1
  omega

abbrev delayedPair : Ground := .unary .fst
  (.binary .pair (.binary .pair target (.const .bottom)) (.const .one))
abbrev delayedKey : Ground := .unary .fst (.binary .pair (.name 70) (.const .bottom))
abbrev ciphertext : Ground := .ternary .penc (.unary .pk (.name 70)) (.name 80) target
abbrev delayedPartial : Ground := .unary .fst
  (.binary .pair (.binary .partialDecrypt (.name 70) ciphertext) (.const .bottom))

/-- Each nonliteral source has an actual reachable pair or E5/E6 match and the
independently specified partial-decryption output. -/
theorem delayed_partial_output_paths :
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
  exact ⟨hp, hp.projection_partialDecrypt_inversion (Or.inl rfl), hd,
    hd.decryption_partialDecrypt_inversion, hs, hs.decryption_partialDecrypt_inversion⟩

/-- A further projection from an honest ciphertext field cannot expose a
partial-decryption value. The literal constructor above remains available. -/
theorem ballot_field_projection_is_not_partial (swap : Bool) :
    ¬ EqE ((world swap).eval (.unary .fst ((Term.var 1).project 0))) target :=
  voter_projection_not_partialDecrypt names swap left right 0
    (.step .fst (Or.inl rfl) (.project 1 0)) _ _

abbrev publishedFrame : Frame names.restricted 1 := ⟨fun _ => target⟩

/-- Publishing a partial decryption invalidates the initial-frame origin claim:
a one-node handle is minimum and has that value without constructor syntax.
This artificial frame is a premise control, not the historical final frame. -/
theorem initial_frame_required :
    MinimalRecipe names.restricted publishedFrame.value (.var 0) ∧
    EqE (publishedFrame.eval (.var 0)) target ∧
    ¬ (∃ a b : Recipe 1, (Term.var 0 : Recipe 1) = .binary .partialDecrypt a b) := by
  refine ⟨MinimalRecipe.of_nodeCount_one trivial rfl, .refl _, ?_⟩
  rintro ⟨a, b, h⟩
  cases h

/-- The full branch has unequal three-node minima and a six-node bound.
Diagonal candidate assignments discharge the bounded premise without assuming
static equivalence of different votes. -/
theorem minimum_partial_step_inhabited :
    MinimalRecipe names.restricted (frame names false left left).value literal ∧
    MinimalRecipe names.restricted (frame names false left left).value reversed ∧
    literal.nodeCount + reversed.nodeCount = 6 ∧
    ¬ EqE ((frame names false left left).eval literal) ((frame names false left left).eval reversed) ∧
    (EqE ((frame names false left left).eval literal) ((frame names false left left).eval reversed) ↔
      EqE ((frame names true left left).eval literal) ((frame names true left left).eval reversed)) := by
  have hr := literal_partial_minimum false left left 40 50 (by decide) (by decide)
  have hs := literal_partial_minimum false left left 50 40 (by decide) (by decide)
  refine ⟨hr, hs, rfl, ?_, minimum_partial_decryption_equality_swap names left left literal reversed hr hs
    (k := .name 40) (c := .name 50) (k' := .name 50) (c' := .name 40) (.refl _) (.refl _)
    (CiphertextObservationSPOT.diagonal_observations _)⟩
  intro he
  have hn := (EqE.name_iff 40 50).mp ((EqE.partialDecrypt_iff _ _ _ _).mp he).1
  omega

end ExplainableCrypto.Helios.Symbolic.PartialDecryptionObservationSPOT
