import ExplainableCrypto.Helios.Symbolic.ExpandedProofTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedOriginSPOT

namespace ExplainableCrypto.Helios.Symbolic.ExpandedProofSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []

private theorem numeric (swap : Bool) : ExpandedResultsNumeric names swap left right [] :=
  accepted_expanded_results_numeric names HistoricalFrameSPOT.fixture_names_fresh left right [] (by simp) trivial swap

/-- All four arguments may be published handles. A nested partial in the nonce
position is minimum and cannot recover either kind of honest proof nonce. -/
theorem constructed_minimum_with_nested_nonce (swap : Bool) :
    let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
    let b := Term.binary .partialDecrypt a (.var (expandedResult 1))
    let c : Recipe (ExpandedHandles 1) := .var (expandedResult 0)
    let d : Recipe (ExpandedHandles 1) := .var (expandedOld 0)
    MinimalRecipe names.restricted (world swap).value (.spk a b c d) ∧
    ¬ EqE ((world swap).eval (.spk a b c d)) (componentProof names 0 (choice swap left right 0).value 0) ∧
    ¬ EqE ((world swap).eval (.spk a b c d)) (aggregateProof names 0 (choice swap left right 0).value) := by
  let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
  let b := Term.binary .partialDecrypt a (.var (expandedResult 1))
  let c : Recipe (ExpandedHandles 1) := .var (expandedResult 0)
  let d : Recipe (ExpandedHandles 1) := .var (expandedOld 0)
  have hb : MinimalRecipe names.restricted (world swap).value b :=
    expanded_minimum_partial_of_children names swap left right [] (by simp) (numeric swap) a (.var (expandedResult 1))
      (.of_nodeCount_one trivial rfl) (.of_nodeCount_one trivial rfl)
  exact ⟨expanded_minimum_spk_of_children names swap left right [] (by simp) (numeric swap) a b c d
      (.of_nodeCount_one trivial rfl) hb (.of_nodeCount_one trivial rfl) (.of_nodeCount_one trivial rfl),
    expanded_constructed_proof_not_component names swap left right [] (by simp) a b c d hb.isPublic 0 0,
    expanded_constructed_proof_not_aggregate names swap left right [] (by simp) a b c d hb.isPublic 0⟩

/-- Publication preserves the one-candidate component/aggregate coincidence,
including the fact that their selector recipes have different syntax. -/
theorem one_candidate_fields_coincide (swap : Bool) :
    let φ := expandedFrame ProofObservationSPOT.oneNames swap ProofObservationSPOT.oneLeft ProofObservationSPOT.oneRight []
    ((Term.var (expandedOld (n := 0) 1)).project 1) ≠ (Term.var (expandedOld 1)).project 2 ∧
    EqE (φ.eval ((Term.var (expandedOld 1)).project 1)) (φ.eval ((Term.var (expandedOld 1)).project 2)) := by
  refine ⟨by decide,?_⟩
  exact (expanded_component_proof_value ProofObservationSPOT.oneNames swap ProofObservationSPOT.oneLeft ProofObservationSPOT.oneRight [] 0 0).trans
    (((component_aggregate_proof_equality_iff ProofObservationSPOT.oneNames NumericReflectionSPOT.fixture_names_fresh
      swap ProofObservationSPOT.oneLeft ProofObservationSPOT.oneRight 0 0 0).mpr ⟨rfl,rfl⟩).trans
      (expanded_aggregate_proof_value ProofObservationSPOT.oneNames swap ProofObservationSPOT.oneLeft ProofObservationSPOT.oneRight [] 0).symm)

/-- The same field categories are separated for two candidates. -/
theorem two_candidate_fields_separate (swap : Bool) :
    ¬ EqE ((world swap).eval ((Term.var (expandedOld 1)).project 3))
      ((world swap).eval ((Term.var (expandedOld 1)).project 4)) := by
  intro he
  have h := (expanded_component_proof_value names swap left right [] 0 1).symm.trans
    (he.trans (expanded_aggregate_proof_value names swap left right [] 0))
  have hn := ((component_aggregate_proof_equality_iff names HistoricalFrameSPOT.fixture_names_fresh
    swap left right 0 0 1).mp h).1
  omega

/-- The accepted minimum equality interface compares the fourth argument,
with the first three fixed published values. It has unequal concrete outputs. -/
theorem fourth_argument_observed :
    let φ := expandedFrame names false left left []
    let ψ := expandedFrame names true left left []
    let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
    let r := Term.spk a a a (.name 40)
    let s := Term.spk a a a (.name 41)
    MinimalRecipe names.restricted φ.value r ∧ MinimalRecipe names.restricted φ.value s ∧
    (EqE (φ.eval r) (φ.eval s) ↔ EqE (ψ.eval r) (ψ.eval s)) ∧ ¬ EqE (φ.eval r) (φ.eval s) := by
  let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
  have hn := accepted_expanded_results_numeric names HistoricalFrameSPOT.fixture_names_fresh left left [] (by simp) trivial false
  have ha : MinimalRecipe names.restricted (expandedFrame names false left left []).value a := .of_nodeCount_one trivial rfl
  have h40 : (Term.name 40 : Recipe (ExpandedHandles 1)).Public names.restricted := by change 40 ∉ names.restricted; decide
  have h41 : (Term.name 41 : Recipe (ExpandedHandles 1)).Public names.restricted := by change 41 ∉ names.restricted; decide
  have hr := expanded_minimum_spk_of_children names false left left [] (by simp) hn a a a (.name 40)
    ha ha ha (.of_nodeCount_one h40 rfl)
  have hs := expanded_minimum_spk_of_children names false left left [] (by simp) hn a a a (.name 41)
    ha ha ha (.of_nodeCount_one h41 rfl)
  refine ⟨hr,hs,accepted_expanded_minimum_proof_equality_swap names HistoricalFrameSPOT.fixture_names_fresh
    left left [] (by simp) trivial _ _ hr hs (.refl _) (.refl _) (fun _ _ _ _ _ => Iff.rfl),?_⟩
  intro he
  exact absurd ((EqE.name_iff 40 41).mp ((EqE.spk_iff _ _ _ _ _ _ _ _).mp he).2.2.2) (by decide)

/-- An honest proof has a borrowed minimum representative in the actual
expanded frame; the origin branch is not merely a syntactic possibility. -/
theorem borrowed_minimum_inhabited (swap : Bool) :
    ∃ r : Recipe (ExpandedHandles 1), MinimalRecipe names.restricted (world swap).value r ∧
      ExpandedBorrowedProofForm r ∧
      EqE ((world swap).eval r) (componentProof names 0 (choice swap left right 0).value 1) := by
  let p : Recipe (ExpandedHandles 1) := (Term.var (expandedOld 1)).project 3
  obtain ⟨r,hr,he⟩ := exists_minimal_recipe (σ := (world swap).value) p (by trivial)
  have hv := he.symm.trans (expanded_component_proof_value names swap left right [] 0 1)
  rcases accepted_expanded_minimum_proof_form names HistoricalFrameSPOT.fixture_names_fresh
      left right [] (by simp) trivial swap r hr hv with ⟨a,b,c,d,rfl⟩ | hborrow
  · exact False.elim (expanded_constructed_proof_not_component names swap left right [] (by simp) a b c d hr.isPublic.2.1 0 1 hv)
  · exact ⟨r,hr,hborrow,hv⟩

/-- A projection wrapper computes a proof, but a shorter public constructor
refutes its minimum status. This is the omitted-minimum mutation control. -/
theorem projection_wrapper_not_minimum (swap : Bool) :
    let p : Recipe (ExpandedHandles 1) := .spk (.name 40) (.name 41) (.name 42) (.name 43)
    let r := Term.unary .fst (.binary .pair p (.name 44))
    EqE ((world swap).eval r) ((world swap).eval p) ∧
    ¬ MinimalRecipe names.restricted (world swap).value r := by
  let p : Recipe (ExpandedHandles 1) := .spk (.name 40) (.name 41) (.name 42) (.name 43)
  have hp : p.Public names.restricted := by
    change 40 ∉ names.restricted ∧ 41 ∉ names.restricted ∧ 42 ∉ names.restricted ∧ 43 ∉ names.restricted
    decide
  refine ⟨.equation (.fst _ _),?_⟩
  intro hm
  have hs := hm.least p hp (.equation (.fst _ _))
  change 8 ≤ 5 at hs
  omega

/-- A projection from either new-handle category cannot return a proof value. -/
theorem new_handle_projection_not_proof (swap : Bool) (j : Fin 2) (a b c d : Ground) :
    ¬ EqE ((world swap).eval (.unary .fst (.var (expandedPartial j)))) (.spk a b c d) ∧
    ¬ EqE ((world swap).eval (.unary .fst (.var (expandedResult j)))) (.spk a b c d) := by
  constructor
  · intro he
    have h := expanded_projection_proof_origin names swap left right [] (numeric swap) (expandedPartial j)
      (.step .fst (by trivial) .handle) he
    rcases h with ⟨i,k,h⟩ | ⟨i,h⟩
    · fin_cases i <;> fin_cases k <;> cases h
    · fin_cases i <;> cases h
  · intro he
    have h := expanded_projection_proof_origin names swap left right [] (numeric swap) (expandedResult j)
      (.step .fst (by trivial) .handle) he
    rcases h with ⟨i,k,h⟩ | ⟨i,h⟩
    · fin_cases i <;> fin_cases k <;> cases h
    · fin_cases i <;> cases h

/-- Structured-key E5 can return a proof assembled from published values.
Its successful decryption wrapper is excluded only from minimum recipes. -/
theorem successful_decryption_returns_proof (swap : Bool) :
    let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
    let p := Term.spk a (.var (expandedResult 0)) (.name 40) (.name 41)
    let b := keyCiphertext a (.name 60) p
    EqE ((world swap).eval (.binary .dec a b)) ((world swap).eval p) ∧
    ¬ MinimalRecipe names.restricted (world swap).value (.binary .dec a b) := by
  let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
  let p := Term.spk a (.var (expandedResult 0)) (.name 40) (.name 41)
  let b := keyCiphertext a (.name 60) p
  have hd : DecryptionMatch ((world swap).eval a) ((world swap).eval b) ((world swap).eval p) :=
    ⟨_,.name 60,Or.inl (.refl _),.refl _⟩
  refine ⟨hd.reduces.sound,?_⟩
  intro hm
  exact accepted_expanded_minimum_decryption_no_match names HistoricalFrameSPOT.fixture_names_fresh
    left right [] (by simp) trivial swap a b hm _ hd

end ExplainableCrypto.Helios.Symbolic.ExpandedProofSPOT
