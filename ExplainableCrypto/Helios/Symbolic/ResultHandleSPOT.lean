import ExplainableCrypto.Helios.Symbolic.ResultNonceSPOT

namespace ExplainableCrypto.Helios.Symbolic.ResultHandleSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []
private theorem numbers (swap : Bool) (j : Fin 2) :
    EqE (tallyResult names swap left right [] j) (addNumeral j.val) := by
  fin_cases j
  · exact (SharedTallySPOT.nonliteral_two_candidate_tally).1 swap
  · exact ((SharedTallySPOT.nonliteral_two_candidate_tally).2 swap).trans (EqE.equation .zero_one).symm

/-- Nested zero/one handles have a single old recipe realization. In
particular zero remains a nonempty constant under the public numeral map. -/
theorem nested_zero_one_realization (swap : Bool) :
    let r : Recipe (ResultHandles 1) := .binary .pair (.var (resultSlot 0)) (.unary .pk (.var (resultSlot 1)))
    EqE ((world swap).eval (r.subst (fun i => .var (resultEmbedding i))))
      ((frame names swap left right).eval (.binary .pair (.const .zero) (.unary .pk (addNumeral 1)))) ∧
    (resultNumeralRecipes (n := 1) (fun j => j.val) (resultSlot 0)).nodeCount=1 := by
  refine ⟨?_,rfl⟩
  exact result_recipe_value names swap left right [] (fun j => j.val) (numbers swap)
      (.binary .pair (.var (resultSlot 0)) (.unary .pk (.var (resultSlot 1))))

/-- A real accepted nonempty election's result two is realized even inside a
public-key constructor; result erasure is not restricted to zero/one bits. -/
theorem nested_two_realization (swap : Bool) :
    let φ := ResultNonceSPOT.world swap
    let r : Recipe (ResultHandles 0) := .unary .pk (.var (resultSlot 0))
    EqE (φ.eval (r.subst (fun i => .var (resultEmbedding i)))) (.unary .pk (addNumeral 2)) := by
  have hnum (j : Fin 1) := by
    have h := ResultNonceSPOT.accepted_numeric_nonce_tally.2 swap
    exact (show EqE (tallyResult ResultNonceSPOT.names swap ResultNonceSPOT.left ResultNonceSPOT.right ResultNonceSPOT.submissions j)
      (addNumeral 2) from by fin_cases j; exact h)
  have h := result_recipe_value ResultNonceSPOT.names swap ResultNonceSPOT.left ResultNonceSPOT.right ResultNonceSPOT.submissions
    (fun _ => 2) hnum (.unary .pk (.var (resultSlot 0)))
  simpa only [Term.subst,result_numeral_slot,Frame.eval,addNumeral] using h

/-- Full unbounded equality holds for the derived result-only frames despite
different actual honest ballot values. Distinct public names remain unequal. -/
theorem result_frame_equivalence_noncollapsed :
    Frame.StaticEq (resultFrame names false left right []) (resultFrame names true left right []) ∧
    (resultFrame names false left right []).eval (.var (resultOld 1)) ≠
      (resultFrame names true left right []).eval (.var (resultOld 1)) ∧
    ¬ EqE ((resultFrame names true left right []).eval (.name 40)) ((resultFrame names true left right []).eval (.name 41)) := by
  refine ⟨accepted_result_frame_staticEq names HistoricalFrameSPOT.fixture_names_fresh left right [] (by simp) trivial,by decide,?_⟩
  intro he
  have h := (EqE.name_iff 40 41).mp he
  omega

/-- The minimized raw comparator failure is retained. Numeric E0 equality
must be used even though raw normalization alone produces distinct terms. -/
theorem raw_numeric_comparison_refuted :
    ResultHandleExperiments.checkWith normalizeRaw 0 = false ∧
    ResultHandleExperiments.check 0 = true := by decide

/-- A published trustee partial cannot be erased to bottom. The result-only
presentation does not silently prove privacy for the omitted public handles. -/
theorem partial_erasure_refuted (swap : Bool) :
    ¬ EqE ((world swap).eval (.var (expandedPartial 0))) (.const .bottom) := by
  intro he
  have h : EqE (.binary .partialDecrypt (.name names.secretKey) (tallyCiphertext names swap left right [] 0)) (.const .bottom) := by
    simpa only [Frame.eval,Term.subst,expanded_frame_partial,tallyPartial] using he
  obtain ⟨_,_,hh,_⟩ := h.passive_binary_irreducible_shape (Or.inr rfl) (constant_irreducible .bottom)
  cases hh

/-- The remaining-recipe callback is inhabited for equal candidates, and its
assembled binding transport enters the actual final-frame theorem. -/
theorem remaining_recipe_pipeline_inhabited :
    ExpandedTrusteeBindingTransport names false true left left [] ∧
    ExpandedTrusteeBindingTransport names true false left left [] ∧
    Frame.StaticEq (finalFrame names false left left []) (finalFrame names true left left []) := by
  have h := accepted_expanded_trustee_binding_of_remaining_recipes names HistoricalFrameSPOT.fixture_names_fresh
    false true left left [] (by simp) trivial (fun _ _ _ _ he _ _ => he)
  exact ⟨h,h,accepted_final_staticEq_of_trustee_binding names HistoricalFrameSPOT.fixture_names_fresh left left [] (by simp) trivial h h⟩

end ExplainableCrypto.Helios.Symbolic.ResultHandleSPOT
