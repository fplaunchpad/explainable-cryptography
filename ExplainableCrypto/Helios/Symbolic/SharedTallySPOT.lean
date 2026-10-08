import ExplainableCrypto.Helios.Symbolic.SharedTally
import ExplainableCrypto.Helios.Symbolic.ElectionTallyExperiments

namespace ExplainableCrypto.Helios.Symbolic.SharedTallySPOT
open Historical General
abbrev names := ProofObservationSPOT.oneNames
abbrev left := ProofObservationSPOT.oneLeft
abbrev right := ProofObservationSPOT.oneRight
abbrev world := ProofObservationSPOT.oneWorld
abbrev first := ElectionTallyExperiments.publicBallot 40 .one
abbrev second := ElectionTallyExperiments.publicBallot 41 .zero
abbrev submissions : List (Recipe 3) := [first,second]

private theorem ballot_public (nonce : Nat) (bit : Constant) (hn : nonce ∉ names.restricted) :
    (ElectionTallyExperiments.publicBallot nonce bit).Public names.restricted := by
  apply constructorBallot_public
  · trivial
  · intro _; exact hn
  · intro _; trivial
  · intro _; exact ⟨trivial,hn,trivial,trivial,hn,trivial⟩

private theorem first_public : first.Public names.restricted := ballot_public 40 .one (by decide)
private theorem second_public : second.Public names.restricted := ballot_public 41 .zero (by decide)

private theorem by_raw (t u : Ground) (h : normalizeRaw t = u) : EqE t u :=
  h ▸ (normalizeRaw_reachable t).to_modulo.sound

private theorem first_accepts : Accepted 0 (publicKey names)
    (honestBoardRecipes.map (world false).eval) ((world false).eval first) := by
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · apply by_raw; decide
  · intro j; fin_cases j
    apply by_raw; decide
  · apply by_raw; decide
  · intro earlier hm i j he
    fin_cases i; fin_cases j
    simp only [honestBoardRecipes,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    all_goals
      have h := (normalizeRaw_reachable _).to_modulo.sound.symm.trans
        (he.trans (normalizeRaw_reachable _).to_modulo.sound)
      have hn := (EqE.name_iff _ _).mp ((EqE.penc_iff _ _ _ _ _ _).mp h).2.1
      exact absurd hn (by decide)

private theorem second_accepts : Accepted 0 (publicKey names)
    ((honestBoardRecipes++[first]).map (world false).eval) ((world false).eval second) := by
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · apply by_raw; decide
  · intro j; fin_cases j
    apply by_raw; decide
  · apply by_raw; decide
  · intro earlier hm i j he
    fin_cases i; fin_cases j
    simp only [honestBoardRecipes,List.cons_append,List.nil_append,List.map_cons,List.map_nil,
      List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    all_goals
      have h := (normalizeRaw_reachable _).to_modulo.sound.symm.trans
        (he.trans (normalizeRaw_reachable _).to_modulo.sound)
      have hn := (EqE.name_iff _ _).mp ((EqE.penc_iff _ _ _ _ _ _).mp h).2.1
      exact absurd hn (by decide)

/-- A fresh one ballot followed by a fresh abstention is accepted after the
two different honest ballots in both voting worlds. -/
theorem fresh_sequence_accepted : ∀ swap : Bool,
    (world swap).AcceptsSequence 0 (.var 0) honestBoardRecipes submissions := by
  have hf : (world false).AcceptsSequence 0 (.var 0) honestBoardRecipes submissions :=
    ⟨first_accepts,second_accepts,trivial⟩
  intro swap
  cases swap with
  | false => exact hf
  | true =>
    apply (initial_acceptsSequence_iff names NumericReflectionSPOT.fixture_names_fresh left right
      honestBoardRecipes submissions ?_ ?_).mp hf
    · intro r hr
      simp only [honestBoardRecipes,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> trivial
    · intro r hr
      simp only [submissions,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact first_public
      · exact second_public

private theorem submissions_public : ∀ r ∈ submissions, r.Public names.restricted := by
  intro r hr
  simp only [submissions,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact first_public
  · exact second_public

/-- The actual E6 tally is 0+1+1+0 = 2 in both worlds. It does not saturate
at one; the general theorem supplies swap preservation for this accepted list. -/
theorem fresh_sequence_tally_two :
    (∀ swap : Bool, EqE (tallyResult names swap left right submissions 0) (addNumeral 2)) ∧
    ¬ EqE (tallyResult names true left right submissions 0) (.const .one) := by
  have hf : EqE (tallyResult names false left right submissions 0) (addNumeral 2) :=
    (normalizeRaw_reachable _).to_modulo.sound.trans
      (baseEq_of_addSyntaxSummary_eq (by decide)).sound
  have hs := accepted_sequence_tally_swap names NumericReflectionSPOT.fixture_names_fresh left right
    submissions submissions_public (fresh_sequence_accepted false) 0
  have ht := hs.symm.trans hf
  refine ⟨?_,?_⟩
  · intro swap; cases swap
    · exact hf
    · exact ht
  · intro he
    have h := (irreducible_eqE_iff_base (addNumeral_irreducible 2) (constant_irreducible .one)).mp
      (ht.symm.trans he)
    have hn := congrArg AddSummary.numeric h.add_summary
    exact absurd hn (by decide)

/-- An empty adversarial suffix with two abstaining voters yields zero, not
an invented multiplicative identity or an extra vote. -/
theorem empty_abstaining_tally :
    (∀ swap : Bool, EqE (tallyResult names swap left left [] 0) (.const .zero)) ∧
    (∃ k, k ≤ 2 ∧ ∀ swap : Bool, EqE (tallyResult names swap left left [] 0) (addNumeral k)) := by
  refine ⟨?_,accepted_sequence_tally_numeric names NumericReflectionSPOT.fixture_names_fresh left left []
    (by simp) trivial 0⟩
  intro swap; cases swap
  all_goals
    exact (normalizeRaw_reachable _).to_modulo.sound.trans
      (baseEq_of_addSyntaxSummary_eq (by decide)).sound

/-- Appending the first accepted submission makes its replay fail. -/
theorem repeated_submission_rejected (swap : Bool) :
    ¬ (world swap).AcceptsSequence 0 (.var 0) honestBoardRecipes [first,first] := by
  intro h
  exact accepted_excludes_replay _ _ _ _ (by simp) h.2.1

/-- The already-published honest ballot is rejected immediately. -/
theorem honest_replay_rejected (swap : Bool) :
    ¬ (world swap).AcceptsSequence 0 (.var 0) honestBoardRecipes [.var 1] := by
  intro h
  exact accepted_excludes_replay _ _ _ _ (by simp [honestBoardRecipes]) h.1

/-- The reconstruction theorem determines the independently chosen adversarial
bit: it is one in both worlds, with the public name-40 nonce in both. -/
theorem common_data_recovers_nonce_and_bit :
    ∃ d : SharedBallotData names, d.Explains names left right first ∧ d.bits 0 = .one ∧
      ∀ swap : Bool, EqE ((world swap).eval (d.nonces 0)) (.name 40) := by
  obtain ⟨d,hd⟩ := initial_accepted_common_data names NumericReflectionSPOT.fixture_names_fresh left right
    first first_public honestBoardRecipes first_accepts (by intro i; fin_cases i <;> simp [honestBoardRecipes])
  have hvalues (swap : Bool) : EqE ((world swap).eval (d.nonces 0)) (.name 40) ∧
      EqE (Term.const (d.bits 0) : Ground) (.const .one) := by
    have h := (hd swap 0).symm.trans (normalizeRaw_reachable _).to_modulo.sound
    cases swap
    all_goals exact (EqE.penc_iff _ _ _ _ _ _).mp h |>.2
  refine ⟨d,hd,?_,fun swap => (hvalues swap).1⟩
  rcases d.isBit 0 with hz | ho
  · exact False.elim (zero_not_one (hz ▸ (hvalues false).2))
  · exact ho

/-- The general tally statement includes nonliteral two-candidate honest
votes. With no adversary, candidate zero gets 0 and candidate one gets 1. -/
theorem nonliteral_two_candidate_tally :
    (∀ swap : Bool, EqE (tallyResult LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right [] 0)
      (.const .zero)) ∧
    (∀ swap : Bool, EqE (tallyResult LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right [] 1)
      (.const .one)) := by
  constructor
  all_goals
    intro swap; cases swap
    all_goals
      exact (normalizeRaw_reachable _).to_modulo.sound.trans
        (baseEq_of_addSyntaxSummary_eq (by decide)).sound

/-- Correct decryption cannot be replaced by a rule ignoring the whole
ciphertext binding; the known defect has a checked no-match witness. -/
theorem decryption_binding_required :
    ¬ (∃ m, DecryptionMatch (.binary .partialDecrypt (.name 40) (DecryptionProbeSPOT.cipher 51))
      (DecryptionProbeSPOT.cipher 50) m) := DecryptionProbeSPOT.complete_binding_required.2

end ExplainableCrypto.Helios.Symbolic.SharedTallySPOT
