import ExplainableCrypto.Helios.Symbolic.ExpandedCheckOrigins
import ExplainableCrypto.Helios.Symbolic.ExpandedCheckExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedCheckSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []

private theorem numeric (swap : Bool) : ExpandedResultsNumeric names swap left right [] :=
  accepted_expanded_results_numeric names HistoricalFrameSPOT.fixture_names_fresh left right [] (by simp) trivial swap

private theorem named_second_no_match (a c : Ground) (name : Nat) : ¬ ProofCheckMatch a (.name name) c := by
  rintro ⟨k,r,bit,_,_,hb,_⟩
  have hh := ((name_irreducible name).reducesModulo hb).head_eq
  cases hh

/-- The first old ciphertext projection is a minimum in the actual expanded
frame. Its classified argument reaches a pair in either vote assignment. -/
theorem first_projection_minimum (swap : Bool) :
    MinimalRecipe names.restricted (world swap).value (.unary .fst (.var (expandedOld 1))) ∧
    ExpandedHonestProjectionForm .fst (.var (expandedOld (n := 1) 1)) ∧
    ∀ swap' : Bool, ∃ x y, ReducesModulo ((world swap').eval (.var (expandedOld 1))) (.binary .pair x y) := by
  have hv : EqE ((world swap).eval (.unary .fst (.var (expandedOld 1))))
      (ciphertext names 0 (choice swap left right 0).value 0) := by
    simpa [world,Frame.eval,Term.subst,expanded_frame_old,General.frame,Term.project,Term.drop] using
      ballot_project_ciphertext names 0 (choice swap left right 0).value 0
  have hm : MinimalRecipe names.restricted (world swap).value (.unary .fst (.var (expandedOld 1))) := by
    refine ⟨trivial,?_⟩
    intro r _ he
    exact ciphertext_recipe_size_ge_two (world swap).value _ _ _
      (fun v => expanded_handle_not_ciphertext names swap left right [] (numeric swap) v _ _ _) (he.symm.trans hv)
  obtain ⟨x,y,hp⟩ := expanded_ballot_tail_pair_value names swap left right [] 0 0 (by decide)
  have hf := expanded_minimum_successful_projection_form names swap left right [] (numeric swap) names.restricted .fst
    (Or.inl rfl) (.var (expandedOld 1)) hm hp
  exact ⟨hm,hf,fun swap' => hf.argument_pair_path names swap' left right []⟩

/-- The last tail projection succeeds to bottom but cannot be minimum. -/
theorem empty_tail_projection_not_minimum (swap : Bool) :
    let r : Recipe (ExpandedHandles 1) := .unary .snd ((Term.var (expandedOld 1)).drop 4)
    EqE ((world swap).eval r) (.const .bottom) ∧ ¬ MinimalRecipe names.restricted (world swap).value r := by
  have ht := expanded_ballot_tail_value names swap left right [] 0 5 (by decide)
  have hl : (ballotFields names 0 (choice swap left right 0).value).length = 5 := ballot_fields_length _ _ _
  have hempty : (ballotFields names 0 (choice swap left right 0).value).drop 5 = [] :=
    List.drop_eq_nil_of_le (by rw [hl])
  have hv : EqE ((world swap).eval (.unary .snd ((Term.var (expandedOld 1)).drop 4))) (.const .bottom) := by
    simpa [world,expandedOld,Term.drop,hempty,Term.tuple] using ht
  exact ⟨hv,fun hm => hm.no_smaller (s := .const .bottom) trivial hv (by decide)⟩

abbrev key : Recipe (ExpandedHandles 1) := .unary .pk (.var (expandedPartial 0))
abbrev nonce : Recipe (ExpandedHandles 1) := .binary .partialDecrypt (.var (expandedPartial 0)) (.var (expandedResult 1))
abbrev cipher (bit : Constant) := Term.ternary .penc key nonce (.const bit)
abbrev good (bit : Constant) := ExpandedCheckExperiments.proofCheck key nonce bit

/-- E8 and E9 both succeed with nested published key/nonce arguments. The
successful whole check has a shorter public ok recipe. -/
theorem both_bits_succeed (swap : Bool) :
    EqE ((world swap).eval (good .zero)) (.const .ok) ∧
    EqE ((world swap).eval (good .one)) (.const .ok) ∧
    ¬ MinimalRecipe names.restricted (world swap).value (good .zero) := by
  have hz : EqE ((world swap).eval (good .zero)) (.const .ok) := .equation (.check_zero _ _)
  exact ⟨hz,.equation (.check_one _ _),fun hm => hm.no_smaller (s := .const .ok) trivial hz (by decide)⟩

/-- Successful checks are equal even when the checked ciphertexts differ. -/
theorem successful_checks_not_injective (swap : Bool) :
    EqE ((world swap).eval (good .zero)) ((world swap).eval (good .one)) ∧
    ¬ EqE ((world swap).eval (cipher .zero)) ((world swap).eval (cipher .one)) := by
  refine ⟨(both_bits_succeed swap).1.trans (both_bits_succeed swap).2.1.symm,?_⟩
  intro he
  exact zero_not_one ((EqE.penc_iff _ _ _ _ _ _).mp he).2.2

/-- A changed fourth binding prevents success despite matching key, nonce and
bit arguments. This uses full-E components, not raw matching failure. -/
theorem changed_fourth_binding_fails (swap : Bool) :
    ¬ EqE ((world swap).eval (.ternary .checkspk key (cipher .zero) (.spk key nonce (.const .zero) (.name 90)))) (.const .ok) := by
  intro he
  obtain ⟨r,bit,_,_,hp⟩ := (EqE.check_ok_iff_components _ _ _).mp he
  have hv := ((EqE.spk_iff _ _ _ _ _ _ _ _).mp hp).2.2.2
  obtain ⟨_,_,_,hshape,_⟩ := hv.symm.penc_irreducible_shape (name_irreducible 90)
  cases hshape

/-- A minimum stuck check may use a published partial as its key. The actual
value-based branch compares unequal third arguments with no destination minimum. -/
theorem stuck_check_step_inhabited :
    let φ := expandedFrame names false left left []
    let ψ := expandedFrame names true left left []
    let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
    let r := Term.ternary .checkspk a (.name 41) (.name 50)
    let s := Term.ternary .checkspk a (.name 41) (.name 60)
    MinimalRecipe names.restricted φ.value r ∧ MinimalRecipe names.restricted φ.value s ∧
    (EqE (φ.eval r) (φ.eval s) ↔ EqE (ψ.eval r) (ψ.eval s)) ∧ ¬ EqE (φ.eval r) (φ.eval s) := by
  let φ := expandedFrame names false left left []
  let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
  have hn := accepted_expanded_results_numeric names HistoricalFrameSPOT.fixture_names_fresh left left [] (by simp) trivial false
  have ha : MinimalRecipe names.restricted φ.value a := .of_nodeCount_one trivial rfl
  have hb : MinimalRecipe names.restricted φ.value (.name 41) := .of_nodeCount_one (by change 41 ∉ names.restricted; decide) rfl
  have hc : MinimalRecipe names.restricted φ.value (.name 50) := .of_nodeCount_one (by change 50 ∉ names.restricted; decide) rfl
  have hd : MinimalRecipe names.restricted φ.value (.name 60) := .of_nodeCount_one (by change 60 ∉ names.restricted; decide) rfl
  have hnr := named_second_no_match (φ.eval a) (.name 50) 41
  have hns := named_second_no_match (φ.eval a) (.name 60) 41
  have hr := expanded_minimum_stuck_check_of_children names false left left [] hn names.restricted a (.name 41) (.name 50) ha hb hc hnr
  have hs := expanded_minimum_stuck_check_of_children names false left left [] hn names.restricted a (.name 41) (.name 60) ha hb hd hns
  refine ⟨hr,hs,accepted_expanded_minimum_stuck_check_equality_swap names HistoricalFrameSPOT.fixture_names_fresh
    left left [] (by simp) trivial _ _ hr hs hnr hns (.refl _) (.refl _) (fun _ _ _ _ _ => Iff.rfl),?_⟩
  intro he
  have ht := ((EqE.proof_check_iff_of_no_match _ _ _ _ _ _ hnr hns).mp he).2.2
  exact absurd ((EqE.name_iff 50 60).mp ht) (by decide)

/-- A successful projection wrapper computes a stuck-check value while
violating minimum size and the exact raw check syntax. -/
theorem projection_wrapper_requires_minimum (swap : Bool) :
    let p : Recipe (ExpandedHandles 1) := .ternary .checkspk (.name 40) (.name 41) (.name 42)
    let r := Term.unary .fst (.binary .pair p (.name 43))
    EqE ((world swap).eval r) ((world swap).eval p) ∧
    ¬ MinimalRecipe names.restricted (world swap).value r ∧
    ¬ (∃ a b c, r = .ternary .checkspk a b c) := by
  let p : Recipe (ExpandedHandles 1) := .ternary .checkspk (.name 40) (.name 41) (.name 42)
  have hp : p.Public names.restricted := by change 40 ∉ names.restricted ∧ 41 ∉ names.restricted ∧ 42 ∉ names.restricted; decide
  refine ⟨.equation (.fst _ _),fun hm => hm.no_smaller (s := p) hp (.equation (.fst _ _)) (by decide),?_⟩
  rintro ⟨a,b,c,h⟩
  cases h

/-- Structured-key E5 may return a stuck check through a nonminimum wrapper.
The minimum-origin proof excludes that wrapper without disabling E5. -/
theorem successful_decryption_returns_stuck_check (swap : Bool) :
    let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
    let p := Term.ternary .checkspk a (.name 41) (.name 50)
    let b := keyCiphertext a (.name 60) p
    EqE ((world swap).eval (.binary .dec a b)) ((world swap).eval p) ∧
    ¬ ProofCheckMatch ((world swap).eval a) (.name 41) (.name 50) ∧
    ¬ MinimalRecipe names.restricted (world swap).value (.binary .dec a b) := by
  let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
  let p := Term.ternary .checkspk a (.name 41) (.name 50)
  let b := keyCiphertext a (.name 60) p
  have hd : DecryptionMatch ((world swap).eval a) ((world swap).eval b) ((world swap).eval p) :=
    ⟨_,.name 60,Or.inl (.refl _),.refl _⟩
  refine ⟨hd.reduces.sound,named_second_no_match _ _ _,?_⟩
  intro hm
  exact expanded_minimum_decryption_no_match names swap left right [] (numeric swap) names.restricted a b hm _ hd

end ExplainableCrypto.Helios.Symbolic.ExpandedCheckSPOT
