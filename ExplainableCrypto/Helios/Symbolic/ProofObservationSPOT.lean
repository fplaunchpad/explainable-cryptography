import ExplainableCrypto.Helios.Symbolic.ProofObservationInduction
import ExplainableCrypto.Helios.Symbolic.CiphertextObservationSPOT

namespace ExplainableCrypto.Helios.Symbolic.ProofObservationSPOT
open Historical General
abbrev names := CiphertextObservationSPOT.names
abbrev left := CiphertextObservationSPOT.left
abbrev right := CiphertextObservationSPOT.right
abbrev world := CiphertextObservationSPOT.world
abbrev oneNames := NumericReflectionSPOT.names
abbrev oneLeft := NumericReflectionSPOT.abstain
abbrev oneRight := NumericReflectionSPOT.selected
abbrev oneWorld (swap : Bool) := frame oneNames swap oneLeft oneRight

/-- Distinct source fields coincide when the nonempty fold has one component.
This is the retained counterexample to unconditional proof-tag separation. -/
theorem one_candidate_fields_coincide (swap : Bool) :
    ((Term.var 1 : Recipe 3).project 1) ≠ (Term.var 1).project 2 ∧
    EqE ((oneWorld swap).eval ((Term.var 1).project 1))
      ((oneWorld swap).eval ((Term.var 1).project 2)) := by
  refine ⟨by decide, ?_⟩
  exact (component_proof_recipe_value oneNames swap oneLeft oneRight 0 0).trans
    (((component_aggregate_proof_equality_iff oneNames NumericReflectionSPOT.fixture_names_fresh
      swap oneLeft oneRight 0 0 0).mpr ⟨rfl, rfl⟩).trans
      (aggregate_proof_recipe_value oneNames swap oneLeft oneRight 0).symm)

theorem two_candidate_fields_separate (swap : Bool) :
    ¬ EqE (componentProof names 0 (choice swap left right 0).value 1)
      (aggregateProof names 0 (choice swap left right 0).value) := by
  intro he
  have hn := ((component_aggregate_proof_equality_iff names HistoricalFrameSPOT.fixture_names_fresh
    swap left right 0 0 1).mp he).1
  omega

/-- Equal abstention messages do not make different voters' aggregate proofs equal. -/
theorem same_messages_different_voters :
    ¬ EqE (aggregateProof names 0 right.value) (aggregateProof names 1 right.value) := by
  intro he
  have hi := (aggregate_proof_equality_iff names HistoricalFrameSPOT.fixture_names_fresh
    false right right 0 1).mp he
  have hv := congrArg Fin.val hi
  change 0 = 1 at hv
  omega

abbrev colliding : Names 1 := ⟨10, 11, fun _ _ => 20⟩

/-- Removing fresh nonce provenance permits equal proof values at distinct
voter and candidate positions, even though the source field tags differ. -/
theorem freshness_required :
    EqE (componentProof colliding 0 right.value 0) (componentProof colliding 1 right.value 1) ∧
    ¬ colliding.Fresh := by
  refine ⟨.refl _, ?_⟩
  intro hf
  have hi : ((0 : Fin 2), (0 : Fin 2)) = (1, 0) := hf.2.1 rfl
  have hv := congrArg (fun p => p.1.val) hi
  change 0 = 1 at hv
  omega

abbrev borrowedBinding : Recipe 3 := (Term.var 1).project 0
abbrev constructed : Recipe 3 := .spk (.var 0) (.name 40) (.const .zero) borrowedBinding

/-- Even exposing the actual honest ciphertext as the fourth argument does not
let a constructed proof with a public nonce become an honest proof. -/
theorem constructed_proof_cannot_borrow (swap : Bool) :
    constructed.Public names.restricted ∧
    ¬ EqE ((world swap).eval constructed) (componentProof names 0 (choice swap left right 0).value 0) ∧
    ¬ EqE ((world swap).eval constructed) (aggregateProof names 0 (choice swap left right 0).value) := by
  have hn : (Term.name 40 : Recipe 3).Public names.nonceNames := by change 40 ∉ names.nonceNames; decide
  refine ⟨?_, constructed_proof_not_component names swap left right _ _ _ _ hn 0 0,
    constructed_proof_not_aggregate names swap left right _ _ _ _ hn 0⟩
  change True ∧ 40 ∉ names.restricted ∧ True ∧ True
  decide

abbrev cipher (bit : Constant) : Recipe 3 := .ternary .penc (.var 0) (.name 40) (.const bit)
abbrev proof : Recipe 3 := .spk (.var 0) (.name 40) (.const .zero) (cipher .zero)
abbrev wrappedProof : Recipe 3 := .spk (.var 0) (.name 40) (.const .zero)
  (.unary .fst (.binary .pair (cipher .zero) (.const .bottom)))
abbrev changedBinding : Recipe 3 := .spk (.var 0) (.name 40) (.const .zero) (cipher .one)

/-- Reduction in the bound ciphertext is accepted, but changing its plaintext
is rejected with the first three proof arguments held exactly fixed. -/
theorem fourth_argument_is_observed (swap : Bool) :
    proof.Public names.restricted ∧ wrappedProof.Public names.restricted ∧ changedBinding.Public names.restricted ∧
    EqE ((world swap).eval proof) ((world swap).eval wrappedProof) ∧
    ¬ EqE ((world swap).eval proof) ((world swap).eval changedBinding) := by
  have hn : 40 ∉ names.restricted := by decide
  have hp : proof.Public names.restricted := ⟨trivial, hn, trivial, trivial, hn, trivial⟩
  have hw : wrappedProof.Public names.restricted := ⟨trivial, hn, trivial, ⟨trivial, hn, trivial⟩, trivial⟩
  have hc : changedBinding.Public names.restricted := ⟨trivial, hn, trivial, trivial, hn, trivial⟩
  refine ⟨hp, hw, hc, .spk (.refl _) (.refl _) (.refl _) (RootStep.fst _ _).sound.symm, ?_⟩
  intro he
  have hb := ((EqE.spk_iff _ _ _ _ _ _ _ _).mp he).2.2.2
  exact zero_not_one ((EqE.penc_iff _ _ _ _ _ _).mp hb).2.2

/-- Proof equality observations can be invariant while the selected proof value
itself changes after the vote swap. -/
theorem honest_proof_values_change :
    ¬ EqE (componentProof oneNames 0 (choice false oneLeft oneRight 0).value 0)
      (componentProof oneNames 0 (choice true oneLeft oneRight 0).value 0) := by
  intro he
  exact zero_not_one ((EqE.spk_iff _ _ _ _ _ _ _ _).mp he).2.2.1

/-- Both minimum inputs have actual, unequal proof values. Identical honest
assignments discharge the bounded hypothesis without assuming different-vote
static equivalence; nonliteral candidate representatives remain in the fixture. -/
theorem minimum_proof_step_inhabited :
    ∃ r s : Recipe 3,
      MinimalRecipe names.restricted (frame names false left left).value r ∧
      MinimalRecipe names.restricted (frame names false left left).value s ∧
      ¬ EqE ((frame names false left left).eval r) ((frame names false left left).eval s) ∧
      (EqE ((frame names false left left).eval r) ((frame names false left left).eval s) ↔
        EqE ((frame names true left left).eval r) ((frame names true left left).eval s)) := by
  let a : Recipe 3 := (Term.var 1).project 3
  let b : Recipe 3 := (Term.var 1).project 4
  have hva := component_proof_recipe_value names false left left 0 (1 : Fin 2)
  have hvb := aggregate_proof_recipe_value names false left left 0
  obtain ⟨r, hr, her⟩ := exists_minimal_recipe (σ := (frame names false left left).value) a (by trivial)
  obtain ⟨s, hs, hes⟩ := exists_minimal_recipe (σ := (frame names false left left).value) b (by trivial)
  have vr := her.symm.trans hva
  have vs := hes.symm.trans hvb
  refine ⟨r, s, hr, hs, ?_, minimum_proof_equality_swap names HistoricalFrameSPOT.fixture_names_fresh
    left left r s hr hs vr vs (CiphertextObservationSPOT.diagonal_observations _)⟩
  intro he
  have hc := vr.symm.trans (he.trans vs)
  have hn := ((component_aggregate_proof_equality_iff names HistoricalFrameSPOT.fixture_names_fresh
    false left left 0 0 1).mp hc).1
  omega

end ExplainableCrypto.Helios.Symbolic.ProofObservationSPOT
