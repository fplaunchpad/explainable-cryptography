import ExplainableCrypto.Helios.Symbolic.CiphertextObservationInduction
import ExplainableCrypto.Helios.Symbolic.GeneralMinimumProofs
import ExplainableCrypto.Helios.Symbolic.NonceFoldBounds

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Fresh aggregate nonce folds identify the voter, even when candidate values
are reducible. The proof uses a surviving named factor, not tally equality. -/
theorem honest_nonce_fold_eq_iff (ns : Names n) (hf : ns.Fresh) (i k : Fin 2) :
    EqE (foldCandidates .compose (fun j => (Term.name (ns.nonce i j) : Ground)))
      (foldCandidates .compose (fun j => .name (ns.nonce k j))) ↔ i = k := by
  constructor
  · intro he
    have hb := (irreducible_eqE_iff_base (named_nonce_fold_irreducible (ns.nonce i))
      (named_nonce_fold_irreducible (ns.nonce k))).mp he
    have hi : (Term.name (V := Empty) (ns.nonce i 0)).baseClass ∈
        (foldCandidates .compose (fun j => (Term.name (ns.nonce i j) : Ground))).composeFactors := by
      apply (mem_foldCandidates_compose _ _).mpr
      exact ⟨0, by simp [Term.composeFactors]⟩
    rw [hb.compose_factors] at hi
    obtain ⟨j, hj⟩ := (mem_foldCandidates_compose _ _).mp hi
    have hn : (Term.name (V := Empty) (ns.nonce i 0)).baseClass = (.name (ns.nonce k j) : Ground).baseClass :=
      Multiset.mem_singleton.mp hj
    have hpair : (i, (0 : Fin (n + 1))) = (k, j) :=
      hf.2.1 ((BaseEq.name_iff _ _).mp ((baseClass_eq_iff _ _).mp hn))
    exact congrArg Prod.fst hpair
  · rintro rfl
    exact .refl _

/-- A component nonce equals an aggregate nonce exactly at the one-candidate
boundary and for the same voter. -/
theorem component_nonce_eq_fold_iff (ns : Names n) (hf : ns.Fresh) (i k : Fin 2) (j : Fin (n + 1)) :
    EqE (Term.name (V := Empty) (ns.nonce i j))
      (foldCandidates .compose (fun l => .name (ns.nonce k l))) ↔ n = 0 ∧ i = k := by
  constructor
  · intro he
    have hb := (irreducible_eqE_iff_base (name_irreducible _) (named_nonce_fold_irreducible (ns.nonce k))).mp he
    have hc := congrArg Multiset.card hb.compose_factors
    rw [named_nonce_fold_card] at hc
    have hn : n = 0 := by simp only [Term.composeFactors, Multiset.card_singleton] at hc; omega
    subst n
    fin_cases j
    have hi : (i, (0 : Fin 1)) = (k, 0) := hf.2.1 ((EqE.name_iff _ _).mp he)
    exact ⟨rfl, congrArg Prod.fst hi⟩
  · rintro ⟨hn, rfl⟩
    subst n
    fin_cases j
    exact .refl _

theorem component_proof_equality_iff (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (i k : Fin 2) (j l : Fin (n + 1)) :
    EqE (componentProof ns i (choice swap left right i).value j)
      (componentProof ns k (choice swap left right k).value l) ↔ i = k ∧ j = l := by
  constructor
  · intro he
    have hn := ((EqE.spk_iff _ _ _ _ _ _ _ _).mp he).2.1
    have hi : (i, j) = (k, l) := hf.2.1 ((EqE.name_iff _ _).mp hn)
    exact Prod.mk.inj hi
  · rintro ⟨rfl, rfl⟩
    exact .refl _

theorem aggregate_proof_equality_iff (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (i k : Fin 2) :
    EqE (aggregateProof ns i (choice swap left right i).value)
      (aggregateProof ns k (choice swap left right k).value) ↔ i = k := by
  constructor
  · intro he
    exact (honest_nonce_fold_eq_iff ns hf i k).mp ((EqE.spk_iff _ _ _ _ _ _ _ _).mp he).2.1
  · rintro rfl
    exact .refl _

theorem component_aggregate_proof_equality_iff (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (i k : Fin 2) (j : Fin (n + 1)) :
    EqE (componentProof ns i (choice swap left right i).value j)
      (aggregateProof ns k (choice swap left right k).value) ↔ n = 0 ∧ i = k := by
  constructor
  · intro he
    exact (component_nonce_eq_fold_iff ns hf i k j).mp ((EqE.spk_iff _ _ _ _ _ _ _ _).mp he).2.1
  · rintro ⟨hn, rfl⟩
    subst n
    fin_cases j
    exact .refl _

theorem component_proof_recipe_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (i : Fin 2) (j : Fin (n + 1)) :
    EqE ((frame ns swap left right).eval ((Term.var i.succ).project (n + 1 + j.val)))
      (componentProof ns i (choice swap left right i).value j) := by
  simpa only [Frame.eval, Term.subst_project, Term.subst, frame_voter_handle] using
    ballot_project_proof ns i (choice swap left right i).value j

theorem aggregate_proof_recipe_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (i : Fin 2) :
    EqE ((frame ns swap left right).eval ((Term.var i.succ).project (2 * (n + 1))))
      (aggregateProof ns i (choice swap left right i).value) := by
  simpa only [Frame.eval, Term.subst_project, Term.subst, frame_voter_handle] using
    ballot_project_aggregate ns i (choice swap left right i).value

/-- Constructed proof nonces are public recipes, so they cannot reproduce an
honest component nonce. No proof-validity or board premise is needed. -/
theorem constructed_proof_not_component (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (a r m c : Recipe 3) (hr : r.Public ns.nonceNames)
    (i : Fin 2) (j : Fin (n + 1)) :
    ¬ EqE ((frame ns swap left right).eval (.spk a r m c))
      (componentProof ns i (choice swap left right i).value j) := by
  intro he
  exact frame_nonce_not_deducible ns swap left right r hr (ns.nonce_mem_nonceNames i j)
    ((EqE.spk_iff _ _ _ _ _ _ _ _).mp he).2.1

theorem constructed_proof_not_aggregate (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (a r m c : Recipe 3) (hr : r.Public ns.nonceNames)
    (i : Fin 2) :
    ¬ EqE ((frame ns swap left right).eval (.spk a r m c))
      (aggregateProof ns i (choice swap left right i).value) := by
  intro he
  apply frame_nonce_factor_not_deducible ns swap left right r hr (ns.nonce_mem_nonceNames i 0)
    _ ?_ ((EqE.spk_iff _ _ _ _ _ _ _ _).mp he).2.1
  apply (mem_foldCandidates_compose _ _).mpr
  exact ⟨0, by simp [Term.composeFactors]⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General
