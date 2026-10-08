import ExplainableCrypto.Helios.Symbolic.ExpandedAtomicTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedAtomicExperiments
import ExplainableCrypto.Helios.Symbolic.TrusteePartialSPOT

namespace ExplainableCrypto.Helios.Symbolic.ExpandedAtomicSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []

private theorem result_value (swap : Bool) (j : Fin 2) :
    EqE ((world swap).eval (.var (expandedResult j))) (.const (if j=0 then .zero else .one)) := by
  simpa only [world,Frame.eval,Term.subst,expanded_frame_result] using (TrusteePartialSPOT.both_candidates_match swap j).2

/-- A public name remains deducible and has literal minimum syntax, while the
secret remains unavailable to every public recipe after publication. -/
theorem public_and_secret_names (swap : Bool) :
    (∃ r : Recipe (ExpandedHandles 1), r.Public names.restricted ∧ EqE ((world swap).eval r) (.name 40)) ∧
    (∀ r, MinimalRecipe names.restricted (world swap).value r → EqE ((world swap).eval r) (.name 40) → r = .name 40) ∧
    ¬ (∃ r : Recipe (ExpandedHandles 1), r.Public names.restricted ∧ EqE ((world swap).eval r) (.name names.secretKey)) := by
  refine ⟨(expanded_name_deducible_iff names swap left right [] (by simp) 40).mpr (by decide),?_,?_⟩
  · intro r hm he
    exact expanded_minimum_name_form names swap left right [] (by simp)
      (accepted_expanded_results_numeric names HistoricalFrameSPOT.fixture_names_fresh left right [] (by simp) trivial swap)
      r hm 40 he
  · intro h
    exact (expanded_name_deducible_iff names swap left right [] (by simp) names.secretKey).mp h (by decide)

/-- Both actual constant-valued handles are minimum and differ syntactically
from their literal constants. Literal-only minimum classification is false. -/
theorem published_constant_minima (swap : Bool) (j : Fin 2) :
    MinimalRecipe names.restricted (world swap).value (.var (expandedResult j)) ∧
    EqE ((world swap).eval (.var (expandedResult j))) (.const (if j=0 then .zero else .one)) ∧
    (Term.var (expandedResult (n := 1) j)) ≠ .const (if j=0 then .zero else .one) :=
  ⟨.of_nodeCount_one trivial rfl,result_value swap j,by intro h; cases h⟩

/-- Raw normalization preserves a numeric sum, not a literal zero. Full E
still identifies that result with zero, retaining the gate's oracle correction. -/
theorem raw_result_is_not_literal (swap : Bool) :
    normalizeRaw ((world swap).eval (.var (expandedResult 0))) = .binary .add (.const .zero) (.const .zero) ∧
    normalizeRaw ((world swap).eval (.var (expandedResult 0))) ≠ .const .zero ∧
    EqE ((world swap).eval (.var (expandedResult 0))) (.const .zero) := by
  have hraw : normalizeRaw ((world swap).eval (.var (expandedResult 0))) = .binary .add (.const .zero) (.const .zero) := by
    cases swap <;> decide
  exact ⟨hraw,(by rw [hraw]; intro h; cases h),(by simpa using result_value swap 0)⟩

/-- The complete atomic step has unequal minimum result inputs in actual
swapped elections, with no smaller-observation hypothesis. -/
theorem unequal_results_transfer :
    (EqE ((world false).eval (.var (expandedResult 0))) ((world false).eval (.var (expandedResult 1))) ↔
      EqE ((world true).eval (.var (expandedResult 0))) ((world true).eval (.var (expandedResult 1)))) ∧
    ¬ EqE ((world false).eval (.var (expandedResult 0))) ((world false).eval (.var (expandedResult 1))) := by
  refine ⟨accepted_expanded_minimum_atomic_equality_swap names HistoricalFrameSPOT.fixture_names_fresh
    left right [] (by simp) trivial (.var (expandedResult 0)) (.var (expandedResult 1))
    (.of_nodeCount_one trivial rfl) (.of_nodeCount_one trivial rfl) (.const .zero) (.const .one) rfl rfl
    (by simpa using result_value false 0) (by simpa using result_value false 1),?_⟩
  intro he
  exact zero_not_one ((result_value false 0).symm.trans (he.trans (result_value false 1)))

/-- A literal and result handle are two different minimum recipes for the
same constant. The accepted atomic interface preserves their equality. -/
theorem literal_result_alias_transfer :
    (Term.const .zero : Recipe (ExpandedHandles 1)) ≠ .var (expandedResult 0) ∧
    EqE ((world true).eval (.const .zero)) ((world true).eval (.var (expandedResult 0))) := by
  refine ⟨(by intro h; cases h),?_⟩
  apply (accepted_expanded_minimum_atomic_equality_iff names HistoricalFrameSPOT.fixture_names_fresh false true
    left right [] (by simp) trivial (.const .zero) (.var (expandedResult 0))
    (.of_nodeCount_one trivial rfl) (.of_nodeCount_one trivial rfl) (.const .zero) (.const .zero) rfl rfl
    (.refl _) (by simpa using result_value false 0)).mpr rfl

/-- Mutating the destination result refutes arbitrary-frame atomic transport.
The source handle remains minimum, so minimum size cannot repair this defect. -/
theorem shared_results_are_required :
    let φ : Frame (∅ : Finset Nat) 1 := ⟨fun _ => .const .zero⟩
    let ψ : Frame (∅ : Finset Nat) 1 := ⟨fun _ => .const .one⟩
    MinimalRecipe ∅ φ.value (.var 0) ∧ EqE (φ.eval (.var 0)) (.const .zero) ∧
    ¬ EqE (ψ.eval (.var 0)) (.const .zero) :=
  ⟨.of_nodeCount_one trivial rfl,.refl _,fun h => zero_not_one h.symm⟩

/-- A successful public wrapper computes a name but is not a minimum recipe. -/
theorem name_wrapper_not_minimum (swap : Bool) :
    let r : Recipe (ExpandedHandles 1) := .unary .fst (.binary .pair (.name 40) (.const .bottom))
    EqE ((world swap).eval r) (.name 40) ∧ ¬ MinimalRecipe names.restricted (world swap).value r := by
  refine ⟨.equation (.fst _ _),?_⟩
  intro hm
  exact hm.no_smaller (s := .name 40) (by change 40 ∉ names.restricted; decide) (.equation (.fst _ _)) (by decide)

/-- A one-node result recipe need not have an atomic value. A valid tally of
two cannot equal any ground atom; recipe size and value size remain distinct. -/
theorem result_two_is_not_atomic (swap : Bool) :
    let φ := expandedFrame SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right SharedTallySPOT.submissions
    MinimalRecipe SharedTallySPOT.names.restricted φ.value (.var (expandedResult 0)) ∧
    EqE (φ.eval (.var (expandedResult 0))) (addNumeral 2) ∧
    ∀ t : Ground, t.nodeCount = 1 → ¬ EqE (φ.eval (.var (expandedResult 0))) t := by
  have hv : EqE ((expandedFrame SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right SharedTallySPOT.submissions).eval
      (.var (expandedResult 0))) (addNumeral 2) := by
    simpa only [Frame.eval,Term.subst,expanded_frame_result] using SharedTallySPOT.fresh_sequence_tally_two.1 swap
  refine ⟨.of_nodeCount_one trivial rfl,hv,?_⟩
  intro t ht he
  have hb := (irreducible_eqE_iff_base (addNumeral_irreducible 2) (ground_atom_irreducible ht)).mp (hv.symm.trans he)
  rcases ground_atom_cases ht with ⟨name,rfl⟩ | ⟨c,rfl⟩
  · have hh := hb.head_eq
    cases hh
  · have hn := congrArg AddSummary.numeric hb.add_summary
    cases c <;> exact absurd hn (by decide)

end ExplainableCrypto.Helios.Symbolic.ExpandedAtomicSPOT
