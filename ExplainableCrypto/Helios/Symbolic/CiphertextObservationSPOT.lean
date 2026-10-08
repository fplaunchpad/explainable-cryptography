import ExplainableCrypto.Helios.Symbolic.CiphertextObservationInduction
import ExplainableCrypto.Helios.Symbolic.CiphertextGroupingSPOT

namespace ExplainableCrypto.Helios.Symbolic.CiphertextObservationSPOT
open Historical General
abbrev names := CiphertextGroupingSPOT.names
abbrev left := CiphertextGroupingSPOT.left
abbrev right := CiphertextGroupingSPOT.right
abbrev world := CiphertextGroupingSPOT.world

def groups (i : Fin 3) : CiphertextGroup 1 :=
  if i = 0 then .constructed (.name 40) (.name 80)
  else if i = 1 then .honest (.leaf (0, 1))
  else .mixed (.name 40) (.name 80) (.leaf (0, 1))

def value (swap : Bool) (i : Fin 3) : Ground :=
  .ternary .penc (publicKey names) ((groups i).nonce names (world swap))
    ((groups i).message (world swap) swap left right)

private theorem group_public (i : Fin 3) : (groups i).Public names.nonceNames := by
  fin_cases i <;> simp [groups, CiphertextGroup.Public, Term.Public]
  all_goals decide

/-- All nine pairings of literal public-only, honest-only and mixed groups are
covered in both actual worlds. The three diagonal equalities accompany six separated off-diagonal cases. -/
theorem all_nine_group_comparisons (swap : Bool) (i j : Fin 3) :
    EqE (value swap i) (value swap j) ↔ i = j := by
  have h := CiphertextGroup.ciphertext_eq_iff names HistoricalFrameSPOT.fixture_names_fresh swap left right
    (groups i) (groups j) (group_public i) (group_public j) (publicKey names) (publicKey names)
  change EqE (value swap i) (value swap j) ↔ _ at h
  rw [h]
  fin_cases i <;> fin_cases j <;> simp [groups, CiphertextGroup.Observation, EqE.refl]

/-- Without protection a literal nonce remainder becomes another honest factor,
so the mixed/honest separation theorem would be false. -/
theorem mixed_honest_separation_needs_protection :
    EqE (Term.binary .compose (.name 20) (.name 21) : Ground)
      (combinationNonce names (.mul (.leaf (0, 0)) (.leaf (0, 1)))) ∧
    ¬ ProtectedValue names.nonceNames (Term.name (V := Empty) 20) := by
  refine ⟨.refl _, ?_⟩
  rintro ⟨r, he, hr⟩
  exact nonce_safe_not_eqE_name hr (by decide : 20 ∈ names.nonceNames) he.symm

/-- A positive coherence fixture retains reduction-only key agreement and
repeated honest leaves. The chosen key comparison fits inside the whole tree. -/
theorem wrapped_key_coherence (swap : Bool) :
    CiphertextGroupingSPOT.assembly.Coherent (world swap) ∧
    CiphertextGroupingSPOT.assembly.keyRecipe.nodeCount < CiphertextGroupingSPOT.assembly.recipe.nodeCount :=
  ⟨CiphertextGroupingSPOT.assembly.coherent_of_key_agreement names swap left right _
    (CiphertextGroupingSPOT.syntactically_different_keys_agree swap).2.2,
    CiphertextGroupingSPOT.assembly.keyRecipe_smaller⟩

theorem omitted_key_comparison_rejected (swap : Bool) :
    CiphertextGroupingSPOT.wrongKey.recipe.Public names.restricted ∧
    ¬ CiphertextGroupingSPOT.wrongKey.Coherent (world swap) := by
  refine ⟨(CiphertextGroupingSPOT.wrong_key_cannot_fuse swap).1, ?_⟩
  intro hc
  obtain ⟨k, r, p, he⟩ :=
    (CiphertextGroupingSPOT.wrongKey.coherent_iff_ciphertext_value names swap left right).mp hc
  exact (CiphertextGroupingSPOT.wrong_key_cannot_fuse swap).2 k r p he

abbrev changingKey := MixedCiphertextSPOT.rho
abbrev changingWrappedKey := MixedCiphertextSPOT.sigma
abbrev changingAssembly : CiphertextAssembly 1 :=
  .mul (.constructed changingKey (.name 40) (.const .zero))
    (.constructed changingWrappedKey (.name 41) (.const .one))

/-- Coherence can hold in both worlds while the key value itself changes.
The induction must preserve key equality tests, not pointwise key values. -/
theorem changing_key_values_preserve_coherence :
    changingAssembly.Coherent (world false) ∧ changingAssembly.Coherent (world true) ∧
    ¬ EqE ((world false).eval changingAssembly.keyRecipe) ((world true).eval changingAssembly.keyRecipe) := by
  have hc (swap : Bool) : changingAssembly.Coherent (world swap) :=
    ⟨trivial, trivial, (RootStep.fst _ _).sound.symm⟩
  exact ⟨hc false, hc true, MixedCiphertextSPOT.public_remainder_values_differ⟩

/-- Smaller-observation transfer is an inhabited premise: identical candidate
assignments give identical actual frames. This does not prove the unequal-vote
induction hypothesis used by the full privacy goal. -/
theorem diagonal_observations (bound : Nat) :
    (frame names false left left).ObservationsBelow (frame names true left left) bound := by
  intro r s _ _ _
  exact Iff.rfl

/-- The certificate-free minimum-recipe induction step applies to two actual,
unequal ciphertext values. This diagonal control validates its premises without
assuming the still-open different-vote static-equivalence theorem. -/
theorem minimum_ciphertext_step_inhabited :
    ∃ r s : Recipe 3,
      MinimalRecipe names.restricted (frame names false left left).value r ∧
      MinimalRecipe names.restricted (frame names false left left).value s ∧
      ¬ EqE ((frame names false left left).eval r) ((frame names false left left).eval s) ∧
      (EqE ((frame names false left left).eval r) ((frame names false left left).eval s) ↔
        EqE ((frame names true left left).eval r) ((frame names true left left).eval s)) := by
  let a : CiphertextAssembly 1 := .honest (0, 1)
  let b : CiphertextAssembly 1 := .constructed (.var 0) (.name 40) (.name 80)
  have ha : a.recipe.Public names.restricted := trivial
  have hb : b.recipe.Public names.restricted := by
    change True ∧ 40 ∉ names.restricted ∧ 80 ∉ names.restricted
    decide
  have hva := a.grouped_value names false left left (publicKey names) (EqE.refl _)
  have hvb := b.grouped_value names false left left (publicKey names) (EqE.refl _)
  obtain ⟨r, hr, her⟩ := exists_minimal_recipe (σ := (frame names false left left).value) a.recipe ha
  obtain ⟨s, hs, hes⟩ := exists_minimal_recipe (σ := (frame names false left left).value) b.recipe hb
  have vr := her.symm.trans hva
  have vs := hes.symm.trans hvb
  refine ⟨r, s, hr, hs, ?_, minimum_ciphertext_equality_swap names
    HistoricalFrameSPOT.fixture_names_fresh left left r s hr hs vr vs (diagonal_observations _)⟩
  intro he
  have hn := ((EqE.penc_iff _ _ _ _ _ _).mp (vr.symm.trans (he.trans vs))).2.1
  have hbad := (EqE.name_iff 21 40).mp hn
  omega

end ExplainableCrypto.Helios.Symbolic.CiphertextObservationSPOT
