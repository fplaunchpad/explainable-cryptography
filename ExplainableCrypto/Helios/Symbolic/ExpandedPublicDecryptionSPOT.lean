import ExplainableCrypto.Helios.Symbolic.ExpandedTrusteeBinding
import ExplainableCrypto.Helios.Symbolic.ExpandedSuccessfulDecryptionExperiments
import ExplainableCrypto.Helios.Symbolic.ExpandedSuccessfulCheckSPOT

namespace ExplainableCrypto.Helios.Symbolic.ExpandedPublicDecryptionSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []
abbrev secret : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
abbrev key := Term.unary .pk secret
abbrev cipher : Recipe (ExpandedHandles 1) := .ternary .penc key (.name 40) (.var (expandedOld 1))
abbrev direct := Term.binary .dec secret cipher
abbrev publicPartial := Term.binary .partialDecrypt secret cipher
abbrev indirect := Term.binary .dec publicPartial cipher
abbrev tally : Recipe (ExpandedHandles 1) := (tallyRecipe (n := 1) [] 0).subst (fun i => .var (expandedOld i))
private theorem numeric (swap : Bool) : ExpandedResultsNumeric names swap left right [] :=
  accepted_expanded_results_numeric names HistoricalFrameSPOT.fixture_names_fresh left right [] (by simp) trivial swap
private theorem cipher_minimum (swap : Bool) : MinimalRecipe names.restricted (world swap).value cipher :=
  expanded_minimum_penc_of_children names swap left right [] (by simp) (numeric swap) _ _ _
    (expanded_minimum_pk_of_child names swap left right [] (by simp) (numeric swap) secret (.of_nodeCount_one trivial rfl))
    (.of_nodeCount_one (by change 40 ∉ names.restricted; decide) rfl) (.of_nodeCount_one trivial rfl)
private theorem tally_minimum (swap : Bool) : MinimalRecipe names.restricted (world swap).value tally :=
  accepted_expanded_minimum_honest_combination names HistoricalFrameSPOT.fixture_names_fresh swap left right []
    (by simp) trivial (.mul (.leaf (0,0)) (.leaf (1,0)))
private theorem tally_value (swap : Bool) : EqE ((world swap).eval tally) (tallyCiphertext names swap left right [] 0) := by
  rw [expanded_old_recipe_value]
  exact .refl _
private theorem diagonal (swap : Bool) (bound : Nat) : Frame.ObservationsBelow (world swap) (world swap) bound :=
  fun _ _ _ _ _ => Iff.rfl

/-- An actual published trustee partial is also a legal ordinary E5 secret.
Minimum children decrypt in seven nodes to a varying honest ballot handle. -/
theorem published_partial_as_direct_key (swap swap' : Bool) :
    Frame.MinimumChildren (world swap) direct ∧ direct.nodeCount=7 ∧
    (∃ k r p, cipher = .ternary .penc k r p) ∧
    Frame.SharedMinimum (world swap) (world swap') direct ∧
    EqE ((world swap).eval direct) ((world swap).eval (.var (expandedOld 1))) := by
  have hc := cipher_minimum swap
  have hv : EqE ((world swap).eval cipher)
      (.ternary .penc (.unary .pk ((world swap).eval secret)) (.name 40) ((world swap).eval (.var (expandedOld 1)))) := .refl _
  exact ⟨⟨.of_nodeCount_one trivial rfl,hc⟩,rfl,
    expanded_minimum_ciphertext_public_secret_form names swap left right [] (by simp) (numeric swap) cipher secret hc trivial hv,
    ⟨.var (expandedOld 1),.of_nodeCount_one trivial rfl,(RootStep.decrypt _ _ _).sound,(RootStep.decrypt _ _ _).sound⟩,
    public_key_constructed_decryption_transfer _ _ secret key (.name 40) (.var (expandedOld 1)) trivial hc.isPublic (diagonal swap _) (.refl _)⟩

/-- A public partial uses an actual trustee partial as its inner secret.
Full E6 binding returns the same explicit ballot recipe in both assignments. -/
theorem constructed_partial_with_published_inner_key (swap swap' : Bool) :
    Frame.MinimumChildren (world swap) indirect ∧ indirect.nodeCount=13 ∧
    Frame.SharedMinimum (world swap) (world swap') indirect ∧
    EqE ((world swap).eval indirect) ((world swap).eval (.var (expandedOld 1))) := by
  have hc := cipher_minimum swap
  have ha := expanded_minimum_partial_of_children names swap left right [] (by simp) (numeric swap)
    secret cipher (.of_nodeCount_one trivial rfl) hc
  have hs := DecryptionMatch.exists_of_values (show EqE ((world swap).eval cipher)
      (keyCiphertext ((world swap).eval secret) (.name 40) ((world swap).eval (.var (expandedOld 1)))) from .refl _)
    (Or.inr (show EqE ((world swap).eval publicPartial) (.binary .partialDecrypt ((world swap).eval secret) ((world swap).eval cipher)) from .refl _))
  exact ⟨⟨ha,hc⟩,rfl,⟨.var (expandedOld 1),.of_nodeCount_one trivial rfl,
    (RootStep.partial_decrypt _ _ _).sound,(RootStep.partial_decrypt _ _ _).sound⟩,
    public_partial_constructed_decryption_transfer _ _ secret cipher key (.name 40) (.var (expandedOld 1))
      ha.isPublic hc.isPublic (diagonal swap _) hs⟩

/-- Published E6 genuinely consumes a nonconstructed, globally minimum honest
product. Thus the initial-frame all-constructed conclusion cannot be reused. -/
theorem borrowed_tally_requires_residual_case (swap swap' : Bool) :
    Frame.MinimumChildren (world swap) (.binary .dec secret tally) ∧ tally.nodeCount=5 ∧
    (∃ out, DecryptionMatch ((world swap).eval secret) ((world swap).eval tally) out) ∧
    ¬ (∃ k r p, tally = .ternary .penc k r p) ∧
    Frame.SharedMinimum (world swap) (world swap') (.binary .dec secret tally) := by
  have hv := expanded_combination_value names swap left right [] (.mul (.leaf (0,0)) (.leaf (1,0)))
  have hs := DecryptionMatch.exists_of_values hv
    (Or.inr (show EqE ((world swap).eval secret) (.binary .partialDecrypt (.name names.secretKey) ((world swap).eval tally)) from by
      rw [Frame.eval,Term.subst,expanded_frame_partial]
      exact .binary .partialDecrypt (.refl _) (tally_value swap).symm))
  exact ⟨⟨.of_nodeCount_one trivial rfl,tally_minimum swap⟩,rfl,hs,
    (by rintro ⟨k,r,p,h⟩; cases h),
    expanded_bound_tally_shared names swap swap' left right [] 0 tally (tally_value swap) (tally_value swap')⟩

/-- The aggregate partial cannot decrypt just one honest ciphertext. E5 would
reveal the secret, and E6 would erase an honest occurrence from the full binding. -/
theorem incomplete_tally_binding_rejected (swap : Bool) :
    ¬ ∃ out, DecryptionMatch ((world swap).eval secret)
      ((world swap).eval ((Term.var (expandedOld 1)).project 0)) out := by
  intro hs
  obtain ⟨k,r,p,hc,hk⟩ := (DecryptionMatch.exists_iff_values _ _).mp hs
  have hv := expanded_combination_value names swap left right [] (.leaf (0,0))
  have hkey := (EqE.pk_iff _ _).mp ((EqE.penc_iff _ _ _ _ _ _).mp (hv.symm.trans hc)).1
  rcases hk with hd | hp
  · exact (expanded_frame_opaque_protected names swap left right [] (by simp)).name_not_deducible secret trivial
      (by simp [Names.restricted]) (hd.trans hkey.symm)
  · have hbind : EqE (tallyCiphertext names swap left right [] 0)
        ((world swap).eval ((Term.var (expandedOld 1)).project 0)) := by
      simp only [Frame.eval,Term.subst,expanded_frame_partial,tallyPartial] at hp
      exact ((EqE.partialDecrypt_iff _ _ _ _).mp hp).2
    exact (tally_minimum swap).no_smaller (s := (Term.var (expandedOld 1)).project 0)
      ((show (Term.var (expandedOld 1) : Recipe (ExpandedHandles 1)).Public names.restricted from trivial).project 0) ((tally_value swap).trans hbind) (by decide)

/-- Old recipe binding transfer covers removable wrappers as well as minima;
its B7 argument does not need any bounded observation premise. -/
theorem wrapped_old_tally_binding (swap swap' : Bool) :
    let r : Recipe 3 := .unary .fst (.binary .pair (tallyRecipe (n := 1) [] 0) (.const .bottom))
    let b := r.subst (fun i => .var (expandedOld (n := 1) i))
    Frame.SharedMinimum (world swap) (world swap') (.binary .dec secret b) ∧
    ¬ MinimalRecipe names.restricted (world swap).value b := by
  let r : Recipe 3 := .unary .fst (.binary .pair (tallyRecipe (n := 1) [] 0) (.const .bottom))
  let b := r.subst (fun i => .var (expandedOld (n := 1) i))
  have hr : r.Public names.restricted := ⟨tallyRecipe_public [] 0 names.restricted (by simp),trivial⟩
  have hb : EqE ((world swap).eval b) (tallyCiphertext names swap left right [] 0) :=
    (RootStep.fst _ _).sound.trans (tally_value swap)
  have hb' := (expanded_old_tally_binding_swap names HistoricalFrameSPOT.fixture_names_fresh swap swap' left right []
    (by simp) r hr 0).mp hb
  refine ⟨expanded_bound_tally_shared names swap swap' left right [] 0 b hb hb',?_⟩
  intro hm
  exact hm.no_smaller (tally_minimum swap).isPublic (RootStep.fst _ _).sound (by decide)

/-- Dropping the ciphertext minimum hypothesis would invalidate raw-constructor
classification, even though ordinary decryption still succeeds. -/
theorem constructor_origin_requires_minimum (swap : Bool) :
    let b := Term.unary .fst (.binary .pair cipher (.const .bottom))
    EqE ((world swap).eval (.binary .dec secret b)) ((world swap).eval (.var (expandedOld 1))) ∧
    ¬ MinimalRecipe names.restricted (world swap).value b ∧
    ¬ (∃ k r p, b = .ternary .penc k r p) := by
  dsimp only
  exact ⟨(EqE.binary .dec (.refl _) (RootStep.fst _ _).sound).trans (RootStep.decrypt _ _ _).sound,
    (fun hm => hm.no_smaller (cipher_minimum swap).isPublic (RootStep.fst _ _).sound (by decide)),
    (by rintro ⟨k,r,p,h⟩; cases h)⟩

/-- Real nonempty accepted submissions yield a published result of two. Its
one-node handle is shared by the retained full-tally decryption in both worlds. -/
theorem nonempty_tally_result_two_shared (swap swap' : Bool) :
    let ns := SharedTallySPOT.names
    let φ := expandedFrame ns swap SharedTallySPOT.left SharedTallySPOT.right SharedTallySPOT.submissions
    let ψ := expandedFrame ns swap' SharedTallySPOT.left SharedTallySPOT.right SharedTallySPOT.submissions
    let b := (tallyRecipe (n := 0) SharedTallySPOT.submissions 0).subst (fun i => .var (expandedOld i))
    Frame.SharedMinimum φ ψ (.binary .dec (.var (expandedPartial 0)) b) ∧
    EqE (φ.eval (.var (expandedResult 0))) (addNumeral 2) := by
  dsimp only
  refine ⟨expanded_bound_tally_shared _ swap swap' _ _ _ 0 _ ?_ ?_,(ExpandedPaddedSPOT.accepted_published_two_is_cheap swap).1⟩
  all_goals rw [expanded_old_recipe_value]; exact .refl _

/-- Equal-candidate frames inhabit the residual binding interface. The complete
local pipeline produces all three presentations without assuming arbitrary B8. -/
theorem binding_pipeline_inhabited :
    ExpandedTrusteeBindingTransport names false true left left [] ∧
    ExpandedTrusteeBindingTransport names true false left left [] ∧
    Frame.StaticEq (expandedFrame names false left left []) (expandedFrame names true left left []) ∧
    Frame.StaticEq (partialFrame names false left left []) (partialFrame names true left left []) ∧
    Frame.StaticEq (finalFrame names false left left []) (finalFrame names true left left []) := by
  have h : ExpandedTrusteeBindingTransport names false true left left [] := fun _ _ _ he _ _ => he
  exact ⟨h,h,
    accepted_expanded_staticEq_of_trustee_binding names HistoricalFrameSPOT.fixture_names_fresh left left [] (by simp) trivial h h,
    accepted_partial_staticEq_of_trustee_binding names HistoricalFrameSPOT.fixture_names_fresh left left [] (by simp) trivial h h,
    accepted_final_staticEq_of_trustee_binding names HistoricalFrameSPOT.fixture_names_fresh left left [] (by simp) trivial h h⟩

end ExplainableCrypto.Helios.Symbolic.ExpandedPublicDecryptionSPOT
