import ExplainableCrypto.Helios.Symbolic.PublishedResults
import ExplainableCrypto.Helios.Symbolic.PublishedFrameExperiments

namespace ExplainableCrypto.Helios.Symbolic.PublishedFrameSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world := LocalRootSPOT.world

/-- Every old recipe retains its exact value after both tuple publications. -/
theorem old_recipes_retained (swap : Bool) (r : Recipe 3) :
    (finalFrame names swap left right []).eval r.lift.lift = (world swap).eval r := by
  rw [finalFrame,Frame.eval_extend_lift,partialFrame,Frame.eval_extend_lift]

/-- Both candidates, including the last, retain their actual partial and
result slots. Independent plaintext expectations are zero and one. -/
theorem complete_candidate_slots (swap : Bool) :
    (∀ j : Fin 2, EqE ((finalFrame names swap left right []).eval ((Term.var 3).project j.val))
      (tallyPartial names swap left right [] j)) ∧
    EqE ((finalFrame names swap left right []).eval ((Term.var 4).project 0)) (.const .zero) ∧
    EqE ((finalFrame names swap left right []).eval ((Term.var 4).project 1)) (.const .one) :=
  ⟨fun j => finalFrame_partial_project names swap left right [] j,
    (finalFrame_result_project names swap left right [] 0).trans
      (SharedTallySPOT.nonliteral_two_candidate_tally.1 swap),
    (finalFrame_result_project names swap left right [] 1).trans
      (SharedTallySPOT.nonliteral_two_candidate_tally.2 swap)⟩

/-- Dropping the last partial changes the published tuple under full E, not
merely its raw representation. The remaining tail is bottom instead of a pair. -/
theorem omitted_partial_slot_observable :
    ¬ EqE (Term.tuple [tallyPartial names false left right [] 0])
      ((partialFrame names false left right []).value 3) := by
  intro he
  change EqE (.binary .pair _ (.const .bottom)) (.binary .pair _ (.binary .pair _ (.const .bottom))) at he
  have htail := ((EqE.pair_iff _ _ _ _).mp he).2
  have h := tuple_eqE_pair_nonempty ([] : List Ground) htail
  simp at h

private theorem submitted_public : ∀ r ∈ SharedTallySPOT.submissions,
    r.Public ProofObservationSPOT.oneNames.restricted := by
  have ballot_public (nonce : Nat) (bit : Constant) (hn : nonce ∉ ProofObservationSPOT.oneNames.restricted) :
      (ElectionTallyExperiments.publicBallot nonce bit).Public ProofObservationSPOT.oneNames.restricted := by
    apply constructorBallot_public
    · trivial
    · intro _; exact hn
    · intro _; trivial
    · intro _; exact ⟨trivial,hn,trivial,trivial,hn,trivial⟩
  intro r hr
  simp only [SharedTallySPOT.submissions,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact ballot_public 40 .one (by decide)
  · exact ballot_public 41 .zero (by decide)

/-- The nonempty accepted fixture has a public result computation in the
partial frame, E-equal to the actual result-tuple handle in the final frame. -/
theorem public_result_recipe (swap : Bool) :
    (resultRecipe (n := 0) SharedTallySPOT.submissions).Public ProofObservationSPOT.oneNames.restricted ∧
    EqE ((partialFrame ProofObservationSPOT.oneNames swap ProofObservationSPOT.oneLeft
      ProofObservationSPOT.oneRight SharedTallySPOT.submissions).eval (resultRecipe (n := 0) SharedTallySPOT.submissions))
      ((finalFrame ProofObservationSPOT.oneNames swap ProofObservationSPOT.oneLeft
        ProofObservationSPOT.oneRight SharedTallySPOT.submissions).value 4) :=
  ⟨resultRecipe_public _ _ submitted_public,resultRecipe_value _ _ _ _ _⟩

/-- The actual final result slot is two, with a general voter-count bound;
the expected value comes from the independently checked 0+1+1+0 fixture. -/
theorem final_result_slot_two :
    (∀ swap : Bool, EqE ((finalFrame ProofObservationSPOT.oneNames swap ProofObservationSPOT.oneLeft
      ProofObservationSPOT.oneRight SharedTallySPOT.submissions).eval ((Term.var 4).project 0)) (addNumeral 2)) ∧
    (∃ k, k ≤ 4 ∧ ∀ swap : Bool,
      EqE ((finalFrame ProofObservationSPOT.oneNames swap ProofObservationSPOT.oneLeft
        ProofObservationSPOT.oneRight SharedTallySPOT.submissions).eval ((Term.var 4).project 0)) (addNumeral k)) :=
  ⟨fun swap => (finalFrame_result_project _ _ _ _ _ _).trans (SharedTallySPOT.fresh_sequence_tally_two.1 swap),
    final_result_numeric ProofObservationSPOT.oneNames NumericReflectionSPOT.fixture_names_fresh
      ProofObservationSPOT.oneLeft ProofObservationSPOT.oneRight SharedTallySPOT.submissions
      submitted_public (SharedTallySPOT.fresh_sequence_accepted false) 0⟩

/-- The exact criterion has an inhabited diagonal instance with distinct
public observations; it does not prove its different-vote partial premise. -/
theorem final_criterion_diagonal :
    Frame.StaticEq (finalFrame names false left left []) (finalFrame names true left left []) ∧
    ¬ EqE ((finalFrame names true left left []).eval (.name 40))
      ((finalFrame names true left left []).eval (.name 41)) := by
  refine ⟨(final_frame_staticEq_iff_partial names left left [] (by simp)).mpr (Frame.StaticEq.refl _),?_⟩
  intro he
  exact absurd ((EqE.name_iff 40 41).mp he) (by decide)

/-- Equal aggregate tallies do not permit publication of an individual
ballot's partial decryption. The same public probe returns zero then one. -/
theorem equal_tally_individual_partial_leak :
    (∀ swap : Bool, EqE (tallyResult ProofObservationSPOT.oneNames swap ProofObservationSPOT.oneLeft
      ProofObservationSPOT.oneRight [] 0) (.const .one)) ∧
    EqE ((PublishedFrameExperiments.individualFrame false).eval PublishedFrameExperiments.individualProbe) (.const .zero) ∧
    EqE ((PublishedFrameExperiments.individualFrame true).eval PublishedFrameExperiments.individualProbe) (.const .one) ∧
    ¬ Frame.StaticEq (PublishedFrameExperiments.individualFrame false) (PublishedFrameExperiments.individualFrame true) := by
  have hz : EqE ((PublishedFrameExperiments.individualFrame false).eval PublishedFrameExperiments.individualProbe) (.const .zero) :=
    (normalizeRaw_reachable (V := Empty) ((PublishedFrameExperiments.individualFrame false).eval
      PublishedFrameExperiments.individualProbe)).to_modulo.sound
  have ho : EqE ((PublishedFrameExperiments.individualFrame true).eval PublishedFrameExperiments.individualProbe) (.const .one) :=
    (normalizeRaw_reachable (V := Empty) ((PublishedFrameExperiments.individualFrame true).eval
      PublishedFrameExperiments.individualProbe)).to_modulo.sound
  refine ⟨?_,hz,ho,?_⟩
  · intro swap; cases swap
    all_goals
      exact (normalizeRaw_reachable _).to_modulo.sound.trans
        (baseEq_of_addSyntaxSummary_eq (by decide)).sound
  · intro hs
    have hp : PublishedFrameExperiments.individualProbe.Public ProofObservationSPOT.oneNames.restricted := by
      change True ∧ True
      trivial
    exact zero_not_one (((hs _ (.const .zero) hp trivial).mp hz).symm.trans ho)

/-- The actual trustee partial is a new initial-frame observation: no public
initial recipe can reconstruct even this concrete candidate's partial term. -/
theorem trustee_partial_not_initially_public (swap : Bool) (r : Recipe 3) (hr : r.Public names.restricted) :
    ¬ EqE ((world swap).eval r) (tallyPartial names swap left right [] 1) :=
  initial_secret_partial_not_deducible names swap left right _ r hr

end ExplainableCrypto.Helios.Symbolic.PublishedFrameSPOT
