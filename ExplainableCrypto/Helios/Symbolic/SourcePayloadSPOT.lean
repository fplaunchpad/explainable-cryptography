import ExplainableCrypto.Helios.Symbolic.SourcePayloadAgreement
import ExplainableCrypto.Helios.Symbolic.SourcePayloadExperiments
import ExplainableCrypto.Helios.Symbolic.HistoricalProcessSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourcePayloadSPOT
open Historical General Source

abbrev simpleBody : Term (Option Nat) := .binary .pair (.var none) (.var (some 7))

/-- The new input is substituted while the old variable remains free. -/
theorem input_does_not_capture :
    bindInput simpleBody (.name 40) = .binary .pair (.name 40) (.var 7) ∧
    bindInput simpleBody (.name 40) ≠ .binary .pair (.name 40) (.name 40) := by
  exact ⟨rfl,by decide⟩

abbrev nestedBody : Term (Option (Option Nat)) :=
  .binary .pair (.var none) (.binary .pair (.var (some none)) (.var (some (some 7))))

/-- Lift past the inner binder before instantiating the outer one. The inner
and outer messages must land in different positions. -/
theorem nested_input_order :
    bindInput (nestedBody.subst (liftSubst (inputSubst (.name 40)))) (.name 41) =
      .binary .pair (.name 41) (.binary .pair (.name 40) (.var 7)) ∧
    bindInput (bindInput nestedBody (.name 40)) (.name 41) ≠
      .binary .pair (.name 41) (.binary .pair (.name 40) (.var 7)) := by
  exact ⟨rfl,by decide⟩

/-- Private variable renaming fixes the fresh binder and changes the matching
free occurrences in the input as well as the continuation. -/
theorem renamed_input_agrees :
    bindInput (simpleBody.subst (fun v => .var (v.map (Equiv.swap 7 8))))
      ((Term.var 7).subst (fun v => .var ((Equiv.swap 7 8) v))) =
    (bindInput simpleBody (.var 7)).subst (fun v => .var ((Equiv.swap 7 8) v)) :=
  bindInput_rename (Equiv.swap 7 8) simpleBody (.var 7)

/-- Equal numeric indices do not alias a public handle with a private local. -/
theorem flattening_preserves_public_handles :
    let body : Term (Fin 3 ⊕ Fin 3) := .binary .pair (.var (.inl 1)) (.var (.inr 1))
    body.subst (flattenLocals (fun v => .name (40+v.val))) =
      .binary .pair (.var 1) (.name 41) := rfl

/-- Rewriting an erasable source expression before input binding is sound. -/
theorem rewrite_under_input :
    EqE (bindInput (.unary .fst (.binary .pair (.var none) (.var (some 7)))) (.name 40))
      (Term.name (V := Nat) 40) :=
  bindInput_congr (RootStep.fst _ _).sound (.refl _)

abbrev tallies : Fin 2 → Ground := fun j => if j.val=0 then DecryptionProbeSPOT.cipher 51 else DecryptionProbeSPOT.cipher 50
abbrev privateReply := trusteeMessage (n := 1) (.name 40) (candidateTuple tallies)

/-- Correct tuple selection gives the complete first-candidate partial binding. -/
theorem first_reply_binding :
    EqE (privateReply.project 0) (.binary .partialDecrypt (.name 40) (DecryptionProbeSPOT.cipher 51)) :=
  (EqE.unary .fst ((trusteeMessage_tuple (.name 40) tallies).drop 0)).trans
    (candidateTuple_project (fun j => .binary .partialDecrypt (.name 40) (tallies j)) 0)

/-- Repeating the last candidate's tally in the first result fails full E6.
This is a semantic negative, independent of raw-normal-form comparison. -/
theorem wrong_candidate_not_plaintext :
    ¬ EqE (.binary .dec (privateReply.project 0) ((candidateTuple tallies).project 1)) (.name 90) := by
  intro h
  have hc := (EqE.binary .dec first_reply_binding (candidateTuple_project tallies 1)).symm.trans h
  have hn (m : Ground) : ¬ DecryptionMatch (.binary .partialDecrypt (.name 40) (DecryptionProbeSPOT.cipher 51))
      (DecryptionProbeSPOT.cipher 50) m := fun hm => DecryptionProbeSPOT.complete_binding_required.2 ⟨m,hm⟩
  obtain ⟨_,_,hh,_⟩ := decryption_normal_shape_of_no_match _ _ hn (name_irreducible 90) hc
  cases hh

/-- The actual nonliteral two-candidate fixture returns zero then one, in
both voting worlds. The source result keeps the per-candidate binding. -/
theorem actual_candidate_results (swap : Bool) :
    EqE ((sourceResults LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right []).project 0) (.const .zero) ∧
    EqE ((sourceResults LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right []).project 1) (.const .one) := by
  have he := sourceResults_eqE LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right []
  refine ⟨?_,?_⟩
  · exact ((EqE.unary .fst (he.drop 0)).trans (candidateTuple_project _ 0)).trans
      (SharedTallySPOT.nonliteral_two_candidate_tally.1 swap)
  · exact ((EqE.unary .fst (he.drop 1)).trans (candidateTuple_project _ (1 : Fin 2))).trans
      (SharedTallySPOT.nonliteral_two_candidate_tally.2 swap)

/-- The source expressions inherit the reached nonempty election's all-recipe
privacy, and their result is the independently established tally two. -/
theorem nonempty_source_outputs :
    Frame.StaticEq
      (sourceFinalFrame HistoricalProcessSPOT.names false HistoricalProcessSPOT.left HistoricalProcessSPOT.right
        [HistoricalProcessSPOT.first,HistoricalProcessSPOT.second])
      (sourceFinalFrame HistoricalProcessSPOT.names true HistoricalProcessSPOT.left HistoricalProcessSPOT.right
        [HistoricalProcessSPOT.first,HistoricalProcessSPOT.second]) ∧
    EqE ((sourceResults HistoricalProcessSPOT.names true HistoricalProcessSPOT.left HistoricalProcessSPOT.right
        [HistoricalProcessSPOT.first,HistoricalProcessSPOT.second]).project 0) (addNumeral 2) := by
  have hw := (HistoricalProcessSPOT.two_extra_complete false).wellFormed
  refine ⟨source_final_staticEq _ NumericReflectionSPOT.fixture_names_fresh _ _ _ hw.publicHistory hw.accepted,?_⟩
  have he := sourceResults_eqE HistoricalProcessSPOT.names true HistoricalProcessSPOT.left HistoricalProcessSPOT.right
    [HistoricalProcessSPOT.first,HistoricalProcessSPOT.second]
  exact ((EqE.unary .fst (he.drop 0)).trans (candidateTuple_project _ 0)).trans
    (SharedTallySPOT.fresh_sequence_tally_two.1 true)

/-- The three directed implementation mutants are retained as kernel checks. -/
theorem binding_and_index_mutants_detected :
    SourcePayloadExperiments.capturesOld 0=false ∧ SourcePayloadExperiments.changesPublic 0=false ∧
    SourcePayloadExperiments.repeatsLastTally 0=false := by decide

end ExplainableCrypto.Helios.Symbolic.SourcePayloadSPOT
