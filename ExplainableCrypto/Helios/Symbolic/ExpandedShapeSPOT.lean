import ExplainableCrypto.Helios.Symbolic.ExpandedDecryptionTransport
import ExplainableCrypto.Helios.Symbolic.TrusteePartialSPOT
import ExplainableCrypto.Helios.Symbolic.ExpandedValueShapes
import ExplainableCrypto.Helios.Symbolic.ExpandedCipherKeySPOT
import ExplainableCrypto.Helios.Symbolic.ExpandedShapeExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedShapeSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []

private theorem small_observations (swap swap' : Bool) : (world swap).ObservationsBelow (world swap') 2 := by
  intro r s _ _ hsize
  have := r.nodeCount_pos
  have := s.nodeCount_pos
  omega

/-- The accepted general theorem covers every old, partial and result handle
in both swap directions, with genuine minimum and observation premises. -/
theorem all_handle_shapes_transfer (swap swap' : Bool) (v : Fin (ExpandedHandles 1)) :
    (((world swap).eval (.var v)).PairValue ↔ ((world swap').eval (.var v)).PairValue) ∧
    (((world swap).eval (.var v)).CiphertextValue ↔ ((world swap').eval (.var v)).CiphertextValue) ∧
    (((world swap).eval (.var v)).PartialValue ↔ ((world swap').eval (.var v)).PartialValue) :=
  accepted_expanded_minimum_value_shapes_swap names HistoricalFrameSPOT.fixture_names_fresh
    swap swap' left right [] (by simp) trivial (.var v) (.of_nodeCount_one trivial rfl)
    ((small_observations swap swap').mono (by simp only [Term.nodeCount]; omega))

/-- A size-two honest ciphertext selector inhabits the reflection theorem,
including its tight empty smaller-test budget. -/
theorem honest_ciphertext_shapes_transfer (swap swap' : Bool) :
    let r : Recipe (ExpandedHandles 1) := .unary .fst (.var (expandedOld 1))
    (((world swap).eval r).CiphertextValue ↔ ((world swap').eval r).CiphertextValue) ∧
      ((world swap).eval r).CiphertextValue ∧ ((world swap').eval r).CiphertextValue := by
  let r : Recipe (ExpandedHandles 1) := .unary .fst (.var (expandedOld 1))
  have h := accepted_expanded_minimum_value_shapes_swap names HistoricalFrameSPOT.fixture_names_fresh
    swap swap' left right [] (by simp) trivial r (ExpandedCheckSPOT.first_projection_minimum swap).1
    (small_observations swap swap')
  obtain ⟨_,_,_,_,_,s,m,hv⟩ := ExpandedCipherKeySPOT.honest_minimum_has_one_node_key swap swap'
  have hc : ((world swap').eval r).CiphertextValue := ⟨_,s,m,hv⟩
  exact ⟨h.2.1,h.2.1.mpr hc,hc⟩

/-- Numeric exclusions include a nonliteral value above one; they are not an
assumption that every accepted tally is a bit or a raw literal atom. -/
theorem nonliteral_numeric_has_no_data_shape :
    ¬ (addNumeral (V := Empty) 2).PairValue ∧
    ¬ (addNumeral (V := Empty) 2).CiphertextValue ∧
    ¬ (addNumeral (V := Empty) 2).PartialValue ∧
    (addNumeral (V := Empty) 2).nodeCount > 1 :=
  ⟨(numeric_not_data_shapes 2).1,(numeric_not_data_shapes 2).2.1,
    (numeric_not_data_shapes 2).2.2,by decide⟩

/-- E5 with a published partial as its secret still returns pair data through
an actual public recipe. The wrapper is nonminimum, preventing a false
promotion of the minimum numeric-match theorem to arbitrary decryptions. -/
theorem E5_pair_output_needs_minimum (swap : Bool) :
    let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
    let b := keyCiphertext a (.name 50) (.binary .pair (.name 40) (.name 41))
    (Term.binary .dec a b).Public names.restricted ∧
    EqE ((world swap).eval (.binary .dec a b)) (.binary .pair (.name 40) (.name 41)) ∧
    ¬ MinimalRecipe names.restricted (world swap).value (.binary .dec a b) := by
  let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
  let b := keyCiphertext a (.name 50) (.binary .pair (.name 40) (.name 41))
  have hmatch : DecryptionMatch ((world swap).eval a) ((world swap).eval b)
      (.binary .pair (.name 40) (.name 41)) := ⟨_,.name 50,Or.inl (.refl _),.refl _⟩
  refine ⟨?_,hmatch.reduces.sound,?_⟩
  · change True ∧ True ∧ 50 ∉ names.restricted ∧ 40 ∉ names.restricted ∧ 41 ∉ names.restricted
    decide
  · intro hm
    exact accepted_expanded_minimum_decryption_no_match names HistoricalFrameSPOT.fixture_names_fresh
      left right [] (by simp) trivial swap a b hm _ hmatch

/-- Concrete E6 execution uses the complete original tally binding even when
its ciphertext argument is delayed by a public pair projection. Its output
is tied to the published result and independently equals one. -/
theorem borrowed_E6_output_is_published_result :
    let ns := ProofObservationSPOT.oneNames
    let l := ProofObservationSPOT.oneLeft
    let r := ProofObservationSPOT.oneRight
    let c := tallyCiphertext ns false l r [] 0
    let p : Ground := .binary .add (.const .zero) (.const .one)
    let delayed := Term.unary .fst (.binary .pair c (.name 90))
    DecryptionMatch ((expandedFrame ns false l r []).eval (.var (expandedPartial 0))) delayed p ∧
      EqE p (tallyResult ns false l r [] 0) ∧ EqE p (.const .one) := by
  let ns := ProofObservationSPOT.oneNames
  let l := ProofObservationSPOT.oneLeft
  let r := ProofObservationSPOT.oneRight
  let c := tallyCiphertext ns false l r [] 0
  let p : Ground := .binary .add (.const .zero) (.const .one)
  let nonce : Ground := .binary .compose (.name 20) (.name 21)
  have hc : ReducesModulo c (keyCiphertext (.name 10) nonce p) := by
    exact (normalizeRaw_reachable c).to_modulo
  have hk : ReducesModulo ((expandedFrame ns false l r []).eval (.var (expandedPartial 0)))
      (.binary .partialDecrypt (.name 10) (keyCiphertext (.name 10) nonce p)) := by
    simp only [Frame.eval,Term.subst,expanded_frame_partial,tallyPartial]
    exact hc.context (.binaryRight .partialDecrypt (.name 10) .hole)
  have hb : ReducesModulo (.unary .fst (.binary .pair c (.name 90))) (keyCiphertext (.name 10) nonce p) :=
    (ReducesModulo.single (RootStep.fst c (.name 90)).to_modulo).trans hc
  exact ⟨⟨.name 10,nonce,Or.inr hk,hb⟩,
    expanded_trustee_E6_output ns false l r [] 0 _ hk hb,.equation .zero_one⟩

/-- Permanent binding mutation: candidate-zero's partial does not decrypt
candidate-one's tally, although both corresponding pairs decrypt. -/
theorem wrong_candidate_binding_rejected (swap : Bool) :
    (∃ out, DecryptionMatch (tallyPartial names swap left right [] 0)
      (tallyCiphertext names swap left right [] 0) out) ∧
    (∃ out, DecryptionMatch (tallyPartial names swap left right [] 1)
      (tallyCiphertext names swap left right [] 1) out) ∧
    ¬ (∃ out, DecryptionMatch (tallyPartial names swap left right [] 0)
      (tallyCiphertext names swap left right [] 1) out) :=
  ⟨(TrusteePartialSPOT.both_candidates_match swap 0).1,
    (TrusteePartialSPOT.both_candidates_match swap 1).1,TrusteePartialSPOT.wrong_candidate_rejected swap⟩

/-- The whole-decryption/result test does not fit below the decryption's own
size. The extra allowance is strict and the two-decryption budget pays for it. -/
theorem result_probe_budget_is_strict :
    let r : Recipe (ExpandedHandles 1) := .binary .dec (.name 40) (.name 41)
    let result : Recipe (ExpandedHandles 1) := .var (expandedResult 0)
    ¬ r.nodeCount + result.nodeCount < r.nodeCount ∧
    ¬ r.nodeCount + result.nodeCount < r.nodeCount + 1 ∧
    r.nodeCount + result.nodeCount < r.nodeCount + 2 ∧
    r.nodeCount + 2 ≤ r.nodeCount + r.nodeCount := by decide

/-- The real published E6 decryption has a one-node result alias and therefore
is nonminimum. This is the concrete compression used by the new failure probe. -/
theorem published_E6_probe_is_nonminimum (swap : Bool) (j : Fin 2) :
    let b := (tallyRecipe [] j).subst (fun i => Term.var (expandedOld (n := 1) i))
    let r := Term.binary .dec (.var (expandedPartial j)) b
    EqE ((world swap).eval r) ((world swap).eval (.var (expandedResult j))) ∧
    ¬ MinimalRecipe names.restricted (world swap).value r := by
  let b := (tallyRecipe [] j).subst (fun i => Term.var (expandedOld (n := 1) i))
  have hb : (world swap).eval b = tallyCiphertext names swap left right [] j :=
    expanded_old_recipe_value names swap left right [] (tallyRecipe [] j)
  have he : EqE ((world swap).eval (.binary .dec (.var (expandedPartial j)) b))
      ((world swap).eval (.var (expandedResult j))) := by
    change EqE (.binary .dec ((world swap).eval (.var (expandedPartial j))) ((world swap).eval b)) _
    rw [hb]
    simp only [world,Frame.eval,Term.subst,expanded_frame_partial,expanded_frame_result,tallyResult]
    exact .refl _
  refine ⟨he,?_⟩
  intro hm
  have hsize := hm.least (.var (expandedResult j)) trivial he
  have := b.nodeCount_pos
  simp only [Term.nodeCount] at hsize
  omega

end ExplainableCrypto.Helios.Symbolic.ExpandedShapeSPOT
