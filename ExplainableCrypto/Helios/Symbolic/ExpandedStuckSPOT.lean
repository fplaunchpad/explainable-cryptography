import ExplainableCrypto.Helios.Symbolic.ExpandedStuckTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedShapeSPOT
import ExplainableCrypto.Helios.Symbolic.ExpandedStuckExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedStuckSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []

private theorem numeric (swap : Bool) (l r : CandidateSubstitution 1 Empty) : ExpandedResultsNumeric names swap l r [] :=
  accepted_expanded_results_numeric names HistoricalFrameSPOT.fixture_names_fresh l r [] (by simp) trivial swap

private theorem named_no_pair {a : Ground} {name : Nat} (he : EqE a (.name name)) :
    ∀ x y, ¬ EqE a (.binary .pair x y) := by
  intro x y hp
  obtain ⟨_,_,hh,_⟩ := (hp.symm.trans he).passive_binary_irreducible_shape (Or.inl rfl) (name_irreducible name)
  cases hh

private theorem named_no_match (a : Ground) (name : Nat) : ∀ out, ¬ DecryptionMatch a (.name name) out := by
  rintro out ⟨k,s,_,hb⟩
  have hh := ((name_irreducible name).reducesModulo hb).head_eq
  cases hh

private theorem projection_min (swap : Bool) (l r : CandidateSubstitution 1 Empty) (f : Unary) (hf : f = .fst ∨ f = .snd) :
    MinimalRecipe names.restricted (expandedFrame names swap l r []).value (.unary f (.name 40)) :=
  expanded_minimum_stuck_projection_of_child names swap l r [] (numeric swap l r) names.restricted f hf (.name 40)
    (.of_nodeCount_one (by change 40 ∉ names.restricted; decide) rfl) (named_no_pair (.refl _))

private theorem decryption_min (swap : Bool) (l r : CandidateSubstitution 1 Empty)
    (a b : Nat) (ha : a ∉ names.restricted) (hb : b ∉ names.restricted) :
    MinimalRecipe names.restricted (expandedFrame names swap l r []).value (.binary .dec (.name a) (.name b)) :=
  expanded_minimum_stuck_decryption_of_children names swap l r [] (numeric swap l r) names.restricted (.name a) (.name b)
    (.of_nodeCount_one ha rfl) (.of_nodeCount_one hb rfl) (named_no_match _ b)

/-- Exact size-two selectors and size-three decryptions are genuine minima
in both actual expanded assignments. -/
theorem literal_stuck_minima (swap : Bool) :
    MinimalRecipe names.restricted (world swap).value (.unary .fst (.name 40)) ∧
    MinimalRecipe names.restricted (world swap).value (.unary .snd (.name 40)) ∧
    MinimalRecipe names.restricted (world swap).value (.binary .dec (.name 40) (.name 50)) :=
  ⟨projection_min swap left right .fst (Or.inl rfl),projection_min swap left right .snd (Or.inr rfl),
    decryption_min swap left right 40 50 (by decide) (by decide)⟩

/-- The accepted equality interface is inhabited and distinguishes selectors.
The diagonal election supplies its smaller-observation premise. -/
theorem selector_equality_nonconstant :
    let φ := expandedFrame names false left left []
    let ψ := expandedFrame names true left left []
    let r : Recipe (ExpandedHandles 1) := .unary .fst (.name 40)
    let s : Recipe (ExpandedHandles 1) := .unary .snd (.name 40)
    (EqE (φ.eval r) (φ.eval s) ↔ EqE (ψ.eval r) (ψ.eval s)) ∧ ¬ EqE (φ.eval r) (φ.eval s) := by
  refine ⟨accepted_expanded_minimum_stuck_projection_equality_swap names HistoricalFrameSPOT.fixture_names_fresh
    false true left left [] (by simp) trivial _ _
    (projection_min false left left .fst (Or.inl rfl)) (projection_min false left left .snd (Or.inr rfl))
    .fst .snd (Or.inl rfl) (Or.inr rfl) (named_no_pair (.refl _)) (named_no_pair (.refl _))
    (.refl _) (.refl _) (fun _ _ _ _ _ => Iff.rfl),?_⟩
  intro he
  have hh := ((EqE.projection_iff_of_no_pair .fst .snd (Or.inl rfl) (Or.inr rfl) _ _
    (named_no_pair (.refl _)) (named_no_pair (.refl _))).mp he).1
  cases hh

/-- Distinct minimum decryption keys stay distinguishable through the
arbitrary stuck-value interface and its actual result-probe budget. -/
theorem decryption_equality_nonconstant :
    let φ := expandedFrame names false left left []
    let ψ := expandedFrame names true left left []
    let r : Recipe (ExpandedHandles 1) := .binary .dec (.name 40) (.name 50)
    let s : Recipe (ExpandedHandles 1) := .binary .dec (.name 41) (.name 50)
    (EqE (φ.eval r) (φ.eval s) ↔ EqE (ψ.eval r) (ψ.eval s)) ∧ ¬ EqE (φ.eval r) (φ.eval s) := by
  refine ⟨accepted_expanded_minimum_stuck_decryption_equality_swap names HistoricalFrameSPOT.fixture_names_fresh
    false true left left [] (by simp) trivial _ _
    (decryption_min false left left 40 50 (by decide) (by decide))
    (decryption_min false left left 41 50 (by decide) (by decide))
    (named_no_match _ 50) (named_no_match _ 50) (.refl _) (.refl _) (fun _ _ _ _ _ => Iff.rfl),?_⟩
  intro he
  have hh := ((EqE.decryption_iff_of_no_match _ _ _ _ (named_no_match _ 50) (named_no_match _ 50)).mp he).1
  exact absurd ((EqE.name_iff 40 41).mp hh) (by decide)

/-- Source origin classification permits reducible target arguments. -/
theorem reducible_target_projection (swap : Bool) :
    let target : Ground := .unary .fst (.binary .pair (.name 40) (.name 41))
    ¬ Irreducible target ∧
    EqE ((world swap).eval (.unary .fst (.name 40))) (.unary .fst target) ∧
    ∃ b : Recipe (ExpandedHandles 1), (Term.unary .fst (.name 40) : Recipe (ExpandedHandles 1)) = .unary .fst b ∧
      ∀ x y, ¬ EqE ((world swap).eval b) (.binary .pair x y) := by
  refine ⟨?_,.unary .fst (EqE.equation (.fst (.name 40) (.name 41))).symm,?_⟩
  · intro h
    exact h _ (RootStep.fst (.name 40) (.name 41)).to_modulo
  · exact expanded_minimum_stuck_projection_form names swap left right [] (numeric swap left right) names.restricted
      (.unary .fst (.name 40)) (literal_stuck_minima swap).1 .fst (Or.inl rfl)
      (named_no_pair (EqE.equation (.fst (.name 40) (.name 41))))
      (.unary .fst (EqE.equation (.fst (.name 40) (.name 41))).symm)

/-- A public projection wrapper has a stuck decryption value but lacks its
raw head and minimum size. This preserves the gate's minimized counterexample. -/
theorem nonminimum_wrapper_not_raw_decryption (swap : Bool) :
    let d : Recipe (ExpandedHandles 1) := .binary .dec (.name 40) (.name 41)
    let r := Term.unary .fst (.binary .pair d (.name 50))
    EqE ((world swap).eval r) ((world swap).eval d) ∧
    ¬ MinimalRecipe names.restricted (world swap).value r ∧
    ¬ (∃ a b, r = .binary .dec a b) := by
  refine ⟨.equation (.fst _ _),?_,?_⟩
  · intro hm
    exact hm.raw_irreducible _ (RootStep.fst _ _).to_rewrite
  · rintro ⟨a,b,h⟩
    cases h

/-- Successful projections forget unselected data; the no-pair premise is
necessary for the stuck argument-injectivity rule. -/
theorem successful_projection_not_injective :
    EqE (Term.unary .fst (.binary .pair (.name 40) (.name 41)) : Ground)
      (.unary .fst (.binary .pair (.name 40) (.name 42))) ∧
    ¬ EqE (Term.binary .pair (.name 40) (.name 41) : Ground) (.binary .pair (.name 40) (.name 42)) := by
  refine ⟨(EqE.equation (.fst _ _)).trans (EqE.equation (.fst _ _)).symm,?_⟩
  intro he
  exact absurd ((EqE.name_iff 41 42).mp ((EqE.pair_iff _ _ _ _).mp he).2) (by decide)

/-- A minimum published result has a successful decryption value but no raw
dec head. Exact stuck origins must retain the target no-match premise. -/
theorem successful_E6_target_not_stuck_origin (swap : Bool) (j : Fin 2) :
    let r : Recipe (ExpandedHandles 1) := .var (expandedResult j)
    MinimalRecipe names.restricted (world swap).value r ∧
    EqE ((world swap).eval r) (.binary .dec (tallyPartial names swap left right [] j)
      (tallyCiphertext names swap left right [] j)) ∧
    (∃ out, DecryptionMatch (tallyPartial names swap left right [] j) (tallyCiphertext names swap left right [] j) out) ∧
    ¬ (∃ a b, r = .binary .dec a b) := by
  refine ⟨.of_nodeCount_one trivial rfl,?_,(TrusteePartialSPOT.both_candidates_match swap j).1,?_⟩
  · simp only [world,Frame.eval,Term.subst,expanded_frame_result,tallyResult]
    exact .refl _
  · rintro ⟨a,b,h⟩
    cases h

/-- A new partial handle is a minimum non-pair argument for either selector. -/
theorem published_partial_projection_minimum (swap : Bool) (j : Fin 2) (f : Unary) (hf : f = .fst ∨ f = .snd) :
    MinimalRecipe names.restricted (world swap).value (.unary f (.var (expandedPartial j))) := by
  apply expanded_minimum_stuck_projection_of_child names swap left right [] (numeric swap left right) names.restricted
    f hf (.var (expandedPartial j)) (.of_nodeCount_one trivial rfl)
  intro x y he
  simp only [Frame.eval,Term.subst,expanded_frame_partial,tallyPartial] at he
  have hh := ((EqE.passive_binary_iff .partialDecrypt .pair (Or.inr rfl) (Or.inl rfl) _ _ _ _).mp he).1
  cases hh

/-- Successful E5 can itself return a stuck-decryption value. Its outer
wrapper is nonminimum even though the payload is stuck. -/
theorem successful_E5_returns_stuck_decryption (swap : Bool) :
    let p : Recipe (ExpandedHandles 1) := .binary .dec (.name 40) (.name 41)
    let r := Term.binary .dec (.name 50) (keyCiphertext (.name 50) (.name 60) p)
    EqE ((world swap).eval r) ((world swap).eval p) ∧
    ¬ MinimalRecipe names.restricted (world swap).value r := by
  refine ⟨(RootStep.decrypt _ _ _).sound,?_⟩
  intro hm
  exact hm.raw_irreducible _ (RootStep.decrypt _ _ _).to_rewrite

end ExplainableCrypto.Helios.Symbolic.ExpandedStuckSPOT
