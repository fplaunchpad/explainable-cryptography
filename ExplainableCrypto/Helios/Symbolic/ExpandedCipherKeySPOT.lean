import ExplainableCrypto.Helios.Symbolic.ExpandedCipherKeyTransfer
import ExplainableCrypto.Helios.Symbolic.ExpandedCheckSPOT

namespace ExplainableCrypto.Helios.Symbolic.ExpandedCipherKeySPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []

private theorem different_keys (a b : Nat) (hab : a ≠ b) :
    ¬ (Term.binary .mul (.ternary .penc (.name a) (.name 50) (.const .zero))
      (.ternary .penc (.name b) (.name 51) (.const .one)) : Ground).CiphertextValue := by
  rintro ⟨k,r,m,he⟩
  obtain ⟨_,_,_,_,ha,hb,_,_⟩ := he.mul_penc_inversion
  have ha := ((EqE.penc_iff _ _ _ _ _ _).mp ha).1
  have hb := ((EqE.penc_iff _ _ _ _ _ _).mp hb).1
  exact hab ((EqE.name_iff a b).mp (ha.trans hb.symm))

/-- The accepted minimum theorem has an actual size-two honest selector
instance in both directions. Its smaller key must have size one. -/
theorem honest_minimum_has_one_node_key (swap swap' : Bool) :
    let r : Recipe (ExpandedHandles 1) := .unary .fst (.var (expandedOld 1))
    ∃ k : Recipe (ExpandedHandles 1), k.Public names.restricted ∧ k.nodeCount = 1 ∧
      k.nodeCount < r.nodeCount ∧ EqE ((world swap).eval k) (publicKey names) ∧
      ∃ nonce message, EqE ((world swap').eval r) (.ternary .penc ((world swap').eval k) nonce message) := by
  have hv : EqE ((world swap).eval (.unary .fst (.var (expandedOld 1))))
      (ciphertext names 0 (choice swap left right 0).value 0) := by
    simpa [world,Frame.eval,Term.subst,expanded_frame_old,General.frame,Term.project,Term.drop] using
      ballot_project_ciphertext names 0 (choice swap left right 0).value 0
  have hobs : (world swap).ObservationsBelow (world swap') 2 := by
    intro r s _ _ hsize
    have := r.nodeCount_pos
    have := s.nodeCount_pos
    omega
  obtain ⟨k,hp,hsize,hkey,nonce,message,hv⟩ := accepted_expanded_minimum_ciphertext_key_transfer
    names HistoricalFrameSPOT.fixture_names_fresh swap swap' left right [] (by simp) trivial
    (.unary .fst (.var (expandedOld 1))) (ExpandedCheckSPOT.first_projection_minimum swap).1 hobs hv
  refine ⟨k,hp,?_,hsize,hkey,nonce,message,hv⟩
  have := k.nodeCount_pos
  change k.nodeCount < 2 at hsize
  omega

/-- A key built from both new public value kinds and a reducible alias are
accepted by the generic product induction, including its strict key budget. -/
theorem nested_published_key_product :
    let φ := expandedFrame names false left left []
    let ψ := expandedFrame names true left left []
    let k : Recipe (ExpandedHandles 1) := .unary .pk (.binary .partialDecrypt
      (.var (expandedPartial 0)) (.var (expandedResult 1)))
    let w := Term.unary .fst (.binary .pair k (.name 60))
    let r := Term.binary .mul (.ternary .penc k (.name 40) (.const .zero))
      (.ternary .penc w (.name 41) (.const .one))
    ∃ key : Recipe (ExpandedHandles 1), key.Public names.restricted ∧ key.nodeCount < r.nodeCount ∧
      EqE (φ.eval key) (φ.eval k) ∧ ∃ nonce message,
        EqE (ψ.eval r) (.ternary .penc (ψ.eval key) nonce message) := by
  dsimp only
  let k : Recipe (ExpandedHandles 1) := .unary .pk (.binary .partialDecrypt
    (.var (expandedPartial 0)) (.var (expandedResult 1)))
  have hkp : k.Public names.restricted := by simp [k,Term.Public]
  have h40 : (Term.name 40 : Recipe (ExpandedHandles 1)).Public names.restricted := by change 40 ∉ names.restricted; decide
  have h41 : (Term.name 41 : Recipe (ExpandedHandles 1)).Public names.restricted := by change 41 ∉ names.restricted; decide
  have h60 : (Term.name 60 : Recipe (ExpandedHandles 1)).Public names.restricted := by change 60 ∉ names.restricted; decide
  apply expanded_ciphertext_syntax_key_transfer names false true left left []
    (accepted_expanded_results_numeric names HistoricalFrameSPOT.fixture_names_fresh left left [] (by simp) trivial false)
    (.binary .mul (.ternary .penc k (.name 40) (.const .zero))
      (.ternary .penc (.unary .fst (.binary .pair k (.name 60))) (.name 41) (.const .one)))
    (.mul (.constructed _ _ _) (.constructed _ _ _))
    ⟨⟨hkp,h40,trivial⟩,⟨⟨hkp,h60⟩,h41,trivial⟩⟩ (fun _ _ _ _ _ => Iff.rfl)
  exact (EqE.binary .mul (.refl _) (.ternary .penc (.equation (.fst _ _)) (.refl _) (.refl _))).trans
    (RootStep.homomorphic _ _ _ _ _).sound

/-- Permanent minimized control: full E cannot fuse distinct named keys. -/
theorem distinct_keys_do_not_fuse :
    ¬ (Term.binary .mul (.ternary .penc (.name 40) (.name 50) (.const .zero))
      (.ternary .penc (.name 41) (.name 51) (.const .one)) : Ground).CiphertextValue :=
  different_keys 40 41 (by decide)

/-- Permanent minimized control: raw key inequality coexists with successful
homomorphic fusion under the modeled equations. -/
theorem raw_unequal_keys_fuse :
    let k : Ground := .unary .pk (.name 40)
    let w := Term.unary .fst (.binary .pair k (.name 41))
    k ≠ w ∧ EqE k w ∧ EqE (.binary .mul (.ternary .penc k (.name 50) (.const .zero))
      (.ternary .penc w (.name 51) (.const .one)))
      (.ternary .penc k (.binary .compose (.name 50) (.name 51))
        (.binary .add (.const .zero) (.const .one))) := by
  refine ⟨by decide,(EqE.equation (.fst _ _)).symm,?_⟩
  exact (EqE.binary .mul (.refl _) (.ternary .penc (.equation (.fst _ _)) (.refl _) (.refl _))).trans
    (RootStep.homomorphic _ _ _ _ _).sound

/-- An actual public product loses its ciphertext value when two formerly
aliased handles diverge. This excludes unconditional cross-frame transfer. -/
theorem smaller_key_observations_are_required :
    let φ : Frame ∅ 2 := ⟨fun _ => .name 40⟩
    let ψ : Frame ∅ 2 := ⟨fun i => if i = 0 then .name 40 else .name 41⟩
    let r : Recipe 2 := .binary .mul (.ternary .penc (.var 0) (.name 50) (.const .zero))
      (.ternary .penc (.var 1) (.name 51) (.const .one))
    r.Public ∅ ∧ CiphertextRecipeSyntax r ∧ (φ.eval r).CiphertextValue ∧
      ¬ (ψ.eval r).CiphertextValue ∧ ¬ φ.ObservationsBelow ψ r.nodeCount := by
  refine ⟨by simp [Term.Public],.mul (.constructed _ _ _) (.constructed _ _ _),?_,?_,?_⟩
  · exact ⟨_,_,_,(RootStep.homomorphic _ _ _ _ _).sound⟩
  · exact distinct_keys_do_not_fuse
  · intro h
    have he := (h (.var 0) (.var 1) trivial trivial (by decide)).mp (.refl _)
    exact absurd ((EqE.name_iff 40 41).mp he) (by decide)

/-- Repeating a ciphertext retains both copies in the nonce and plaintext
combinations. No idempotence or global unit law is introduced. -/
theorem repeated_factor_value :
    let a : Ground := .ternary .penc (.name 40) (.name 50) (.const .one)
    let b : Ground := .ternary .penc (.name 40) (.name 51) (.const .zero)
    EqE (.binary .mul a (.binary .mul a b))
      (.ternary .penc (.name 40) (.binary .compose (.name 50) (.binary .compose (.name 50) (.name 51)))
        (.binary .add (.const .one) (.binary .add (.const .one) (.const .zero)))) :=
  (EqE.binary .mul (.refl _) (RootStep.homomorphic _ _ _ _ _).sound).trans
    (RootStep.homomorphic _ _ _ _ _).sound

end ExplainableCrypto.Helios.Symbolic.ExpandedCipherKeySPOT
