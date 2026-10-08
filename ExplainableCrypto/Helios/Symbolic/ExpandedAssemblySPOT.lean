import ExplainableCrypto.Helios.Symbolic.ExpandedCiphertextTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedGroupSPOT
import ExplainableCrypto.Helios.Symbolic.ExpandedAssemblyExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedAssemblySPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []
abbrev key : Recipe (ExpandedHandles 1) := .var (expandedOld 0)
abbrev delayedKey : Recipe (ExpandedHandles 1) := .unary .fst (.binary .pair key (.name 40))
abbrev trustee : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
abbrev result : Recipe (ExpandedHandles 1) := .var (expandedResult 1)
abbrev honest : CiphertextAssembly 1 (ExpandedHandles 1) := .honest (0,0)
abbrev mixed : CiphertextAssembly 1 (ExpandedHandles 1) := .mul
  (.constructed delayedKey trustee result) (.mul honest honest)

private theorem delayed_key_value (swap : Bool) : EqE ((world swap).eval delayedKey) (publicKey names) :=
  .equation (.fst _ _)
private theorem mixed_agreement (swap : Bool) : mixed.KeyAgreement names (world swap) (publicKey names) :=
  ⟨delayed_key_value swap,.refl _,.refl _⟩
private theorem mixed_value (swap : Bool) : ((world swap).eval (mixed.recipeWith expandedOld)).CiphertextValue :=
  ⟨_,_,_,mixed.grouped_valueWith names (world swap) expandedOld swap left right
    (expanded_honest_selector_value names swap left right []) _ (mixed_agreement swap)⟩
private theorem mixed_public : (mixed.recipeWith expandedOld).Public names.restricted := by
  change ((True ∧ 40 ∉ names.restricted) ∧ True ∧ True) ∧ True ∧ True
  decide

/-- Selected constructed keys can be nonliteral and larger than one node.
The original syntax still supplies a strict bound. -/
theorem nonliteral_key_size (swap : Bool) :
    (mixed.keyRecipeWith expandedOld).nodeCount = 4 ∧
    (mixed.keyRecipeWith expandedOld).nodeCount < (mixed.recipeWith expandedOld).nodeCount ∧
    EqE ((world swap).eval (mixed.keyRecipeWith expandedOld)) (publicKey names) :=
  ⟨rfl,mixed.keyRecipeWith_smaller expandedOld,delayed_key_value swap⟩

/-- The exact mixed group retains both honest occurrences and the actual
published partial and result recipes; its bound is below the original size. -/
theorem published_mixed_group_and_bound :
    mixed.group = .mixed trustee result (.mul (.leaf (0,0)) (.leaf (0,0))) ∧
    mixed.group.budget = 5 ∧ (mixed.recipeWith expandedOld).nodeCount = 13 ∧
    mixed.group.Public names.restricted ∧ mixed.group.budget ≤ (mixed.recipeWith expandedOld).nodeCount :=
  ⟨rfl,rfl,rfl,mixed.group_publicWith expandedOld mixed_public,mixed.group_budgetWith expandedOld⟩

/-- Expanded interpretation reconstructs the same key and full nonce/payload
combinations in either assignment, including duplicate honest contributions. -/
theorem actual_mixed_grouped_value (swap : Bool) :
    EqE ((world swap).eval (mixed.recipeWith expandedOld))
      (.ternary .penc ((world swap).eval delayedKey)
        (.binary .compose ((world swap).eval trustee)
          (.binary .compose (.name (names.nonce 0 0)) (.name (names.nonce 0 0))))
        (.binary .add ((world swap).eval result)
          (.binary .add ((choice swap left right 0).value 0) ((choice swap left right 0).value 0)))) :=
  expanded_assembly_grouped_value names swap left right [] mixed (mixed_value swap)

/-- A public constructed key unequal to the election key prevents fusion with
an honest leaf. This is the minimized common-key mutation. -/
theorem wrong_key_honest_product_not_ciphertext (swap : Bool) :
    let t : CiphertextAssembly 1 (ExpandedHandles 1) := .mul
      (.constructed (.name 40) (.name 41) (.const .zero)) honest
    ¬ ((world swap).eval (t.recipeWith expandedOld)).CiphertextValue := by
  dsimp only
  rintro ⟨k,r,p,he⟩
  have hk := CiphertextAssembly.key_agreement_of_valueWith names (world swap) expandedOld swap left right
    (expanded_honest_selector_value names swap left right [])
    (.mul (.constructed (.name 40) (.name 41) (.const .zero)) honest) he
  have bad : EqE (.name 40) (publicKey names) := hk.1.trans hk.2.symm
  obtain ⟨_,hh,_⟩ := bad.symm.pk_irreducible_shape (name_irreducible 40)
  cases hh

/-- A published partial projection cannot become an honest ciphertext leaf.
This retains the invalid-selector mutation as a full-E rejection. -/
theorem partial_selector_not_ciphertext (swap : Bool) :
    ¬ ((world swap).eval (.unary .fst trustee)).CiphertextValue := by
  rintro ⟨k,r,p,he⟩
  have hn := accepted_expanded_results_numeric names HistoricalFrameSPOT.fixture_names_fresh
    left right [] (by simp) trivial swap
  obtain ⟨i,j,_,hr,_⟩ := expanded_projection_ciphertext_origin names swap left right [] hn
    (expandedPartial 0) (ProjectionChain.project _ 0) he
  have hbad : ∀ i : Fin 2, ∀ j : Fin 2,
      (Term.unary .fst trustee) ≠ (Term.var (expandedOld (n := 1) i.succ)).project j.val := by decide
  exact hbad i j hr

/-- Deleting an honest occurrence changes the equality observation even when
both assemblies have valid common keys and identical public contributions. -/
theorem duplicate_assembly_not_equal (swap : Bool) :
    let single : CiphertextAssembly 1 (ExpandedHandles 1) := .mul
      (.constructed delayedKey trustee result) honest
    ¬ EqE ((world swap).eval (mixed.recipeWith expandedOld))
      ((world swap).eval (single.recipeWith expandedOld)) := by
  dsimp only
  let single : CiphertextAssembly 1 (ExpandedHandles 1) := .mul (.constructed delayedKey trustee result) honest
  have hp : (single.recipeWith expandedOld).Public names.restricted := by
    change ((True ∧ 40 ∉ names.restricted) ∧ True ∧ True) ∧ True
    decide
  have hv : ((world swap).eval (single.recipeWith expandedOld)).CiphertextValue :=
    ⟨_,_,_,single.grouped_valueWith names (world swap) expandedOld swap left right
      (expanded_honest_selector_value names swap left right []) _ ⟨delayed_key_value swap,.refl _⟩⟩
  intro he
  have hg := (expanded_assembly_equality_iff names HistoricalFrameSPOT.fixture_names_fresh swap left right []
    (by simp) mixed single mixed_public hp (mixed_value swap) hv).mp he |>.2
  have hc := congrArg Multiset.card hg.1
  change 2 = 1 at hc
  omega

/-- Actual minimum honest selectors obtain the bounded assembly certificate;
the source numeric premise is discharged by acceptance. -/
theorem honest_minimum_assembly (swap : Bool) :
    ∃ t : CiphertextAssembly 1 (ExpandedHandles 1),
      t.recipeWith expandedOld = (Term.unary .fst (.var (expandedOld 1))) ∧
      t.group.Public names.restricted ∧ t.group.budget ≤ 2 ∧
      (t.keyRecipeWith expandedOld).Public names.restricted ∧ (t.keyRecipeWith expandedOld).nodeCount < 2 := by
  exact expanded_minimum_ciphertext_assembly names swap left right []
    (accepted_expanded_results_numeric names HistoricalFrameSPOT.fixture_names_fresh left right [] (by simp) trivial swap)
    _ (ExpandedCheckSPOT.first_projection_minimum swap).1
    ⟨_,_,_,expanded_honest_selector_value names swap left right [] (0,0)⟩

/-- The final minimum equality branch has inhabited premises and rejects a
comparison of different honest nonces. A diagonal election supplies its bounded
observation premise without assuming the unfinished global B8 theorem. -/
theorem minimum_equality_branch_inhabited :
    let φ := expandedFrame names false left left []
    let ψ := expandedFrame names true left left []
    let r : Recipe (ExpandedHandles 1) := .unary .fst (.var (expandedOld 1))
    let s : Recipe (ExpandedHandles 1) := .unary .fst (.var (expandedOld 2))
    MinimalRecipe names.restricted φ.value r ∧ MinimalRecipe names.restricted φ.value s ∧
      (EqE (φ.eval r) (φ.eval s) ↔ EqE (ψ.eval r) (ψ.eval s)) ∧ ¬ EqE (φ.eval r) (φ.eval s) := by
  dsimp only
  let φ := expandedFrame names false left left []
  have hn := accepted_expanded_results_numeric names HistoricalFrameSPOT.fixture_names_fresh
    left left [] (by simp) trivial false
  have hmin (i : Fin 2) : MinimalRecipe names.restricted φ.value (.unary .fst (.var (expandedOld i.succ))) := by
    refine ⟨trivial,?_⟩
    intro r _ he
    exact ciphertext_recipe_size_ge_two φ.value _ _ _
      (fun v => expanded_handle_not_ciphertext names false left left [] hn v _ _ _)
      (he.symm.trans (expanded_honest_selector_value names false left left [] (i,0)))
  have hvr := expanded_honest_selector_value names false left left [] (0,0)
  have hvs := expanded_honest_selector_value names false left left [] (1,0)
  refine ⟨hmin 0,hmin 1,accepted_expanded_minimum_ciphertext_equality_swap names
    HistoricalFrameSPOT.fixture_names_fresh false true left left [] (by simp) trivial _ _
    (hmin 0) (hmin 1) ⟨_,_,_,hvr⟩ ⟨_,_,_,hvs⟩ (fun _ _ _ _ _ => Iff.rfl),?_⟩
  intro he
  have hn := ((EqE.penc_iff _ _ _ _ _ _).mp (hvr.symm.trans (he.trans hvs))).2.1
  exact (by decide : names.nonce 0 0 ≠ names.nonce 1 0) ((EqE.name_iff _ _).mp hn)

end ExplainableCrypto.Helios.Symbolic.ExpandedAssemblySPOT
