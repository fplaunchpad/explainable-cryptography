import ExplainableCrypto.Helios.Symbolic.TrusteePartialBoundary
import ExplainableCrypto.Helios.Symbolic.TrusteePartialExperiments

namespace ExplainableCrypto.Helios.Symbolic.TrusteePartialSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world := LocalRootSPOT.world

private theorem empty_accepted :
    (world false).AcceptsSequence 1 (.var 0) honestBoardRecipes [] := trivial

private theorem tally_public (j : Fin 2) :
    (tallyRecipe [] j).Public names.restricted := tallyRecipe_public [] j _ (by simp)

/-- Both actual candidates decrypt in both assignments; the expectation comes
from the independent nonliteral zero/one candidate fixture. -/
theorem both_candidates_match (swap : Bool) (j : Fin 2) :
    (∃ m, DecryptionMatch (tallyPartial names swap left right [] j)
      (tallyCiphertext names swap left right [] j) m) ∧
    EqE (tallyResult names swap left right [] j) (.const (if j=0 then .zero else .one)) := by
  refine ⟨(accepted_tally_partial_match_iff names HistoricalFrameSPOT.fixture_names_fresh
    left right [] (by simp) empty_accepted swap j (tallyRecipe [] j) (tally_public j)).mpr (.refl _),?_⟩
  fin_cases j
  · exact SharedTallySPOT.nonliteral_two_candidate_tally.1 swap
  · exact SharedTallySPOT.nonliteral_two_candidate_tally.2 swap

private theorem distinct_tallies (swap : Bool) :
    ¬ EqE (tallyCiphertext names swap left right [] 0) (tallyCiphertext names swap left right [] 1) := by
  intro he
  have ht : EqE (tallyResult names swap left right [] 0) (tallyResult names swap left right [] 1) :=
    .binary .dec (.binary .partialDecrypt (.refl _) he) he
  exact zero_not_one ((SharedTallySPOT.nonliteral_two_candidate_tally.1 swap).symm.trans
    (ht.trans (SharedTallySPOT.nonliteral_two_candidate_tally.2 swap)))

/-- Same election key is insufficient: candidate zero's partial cannot decrypt
candidate one's aggregate, even though each candidate separately decrypts. -/
theorem wrong_candidate_rejected (swap : Bool) :
    ¬ (∃ m, DecryptionMatch (tallyPartial names swap left right [] 0)
      (tallyCiphertext names swap left right [] 1) m) := by
  intro hm
  exact distinct_tallies swap ((accepted_tally_partial_match_iff names HistoricalFrameSPOT.fixture_names_fresh
    left right [] (by simp) empty_accepted swap 0 (tallyRecipe [] 1) (tally_public 1)).mp hm).symm

/-- Published partials retain a nontrivial equality pattern, and it transfers. -/
theorem distinct_partial_slots :
    (¬ EqE (tallyPartial names false left right [] 0) (tallyPartial names false left right [] 1)) ∧
    (¬ EqE (tallyPartial names true left right [] 0) (tallyPartial names true left right [] 1)) ∧
    (EqE (tallyPartial names false left right [] 0) (tallyPartial names false left right [] 1) ↔
      EqE (tallyPartial names true left right [] 0) (tallyPartial names true left right [] 1)) :=
  ⟨fun h => distinct_tallies false ((tally_partial_eq_iff names false left right [] 0 1).mp h),
    fun h => distinct_tallies true ((tally_partial_eq_iff names true left right [] 0 1).mp h),
    tally_partial_equality_swap names HistoricalFrameSPOT.fixture_names_fresh left right [] (by simp) 0 1⟩

/-- No old public recipe supplies a ciphertext under this newly published key. -/
theorem no_initial_partial_keyed_cipher (swap : Bool) (r : Recipe 3) (hr : r.Public names.restricted) :
    ¬ EqE ((world swap).eval r)
      (keyCiphertext (tallyPartial names swap left right [] 0) (.name 60) (.name 90)) :=
  initial_ciphertext_not_keyed_by_trustee_partial names swap left right _ _ _ r hr

/-- The same partial does act as an E5 secret for a newly constructed cipher,
with an arbitrary payload. Publication must not delete this branch. -/
theorem new_cipher_uses_partial_as_secret (swap : Bool) (nonce payload : Ground) :
    (∃ m, DecryptionMatch (tallyPartial names swap left right [] 0)
      (keyCiphertext (tallyPartial names swap left right [] 0) nonce payload) m) ∧
    EqE (.binary .dec (tallyPartial names swap left right [] 0)
      (keyCiphertext (tallyPartial names swap left right [] 0) nonce payload)) payload :=
  ⟨⟨payload,_,nonce,Or.inl (.refl _),.refl _⟩,(RootStep.decrypt _ _ _).sound⟩

/-- This E5 case is reachable by a public recipe over the actual extended
frame; it is not just an arbitrary ground-term example. -/
theorem public_new_cipher_decrypts (swap : Bool) :
    let a : Recipe 4 := (Term.var 3).project 0
    let probe := Term.binary .dec a (keyCiphertext a (.name 60) (.name 90))
    probe.Public names.restricted ∧
      EqE ((partialFrame names swap left right []).eval probe) (.name 90) := by
  refine ⟨?_,(RootStep.decrypt _ _ _).sound⟩
  change True ∧ True ∧ 60 ∉ names.restricted ∧ 90 ∉ names.restricted
  decide

/-- A nonliteral old recipe, delayed by a pair projection, matches in both
worlds and the actual published probe returns a shared bounded numeral. -/
theorem delayed_old_probe_numeric :
    let r : Recipe 3 := .unary .fst (.binary .pair (tallyRecipe [] (1 : Fin 2)) (.name 90))
    ∃ k, k ≤ 2 ∧ ∀ swap : Bool,
      EqE ((partialFrame names swap left right []).eval
        (.binary .dec ((Term.var 3).project 1) r.lift)) (addNumeral k) := by
  let r : Recipe 3 := .unary .fst (.binary .pair (tallyRecipe [] (1 : Fin 2)) (.name 90))
  have hr : r.Public names.restricted := ⟨tally_public 1,show 90 ∉ names.restricted by decide⟩
  apply accepted_tally_partial_probe_numeric names HistoricalFrameSPOT.fixture_names_fresh
    left right [] (by simp) empty_accepted 1 r hr
  exact (accepted_tally_partial_match_iff names HistoricalFrameSPOT.fixture_names_fresh
    left right [] (by simp) empty_accepted false 1 r hr).mpr (RootStep.fst _ _).sound

/-- Keeping the secret restricted is load-bearing: the same partial is
constructible as soon as the policy permits the election secret's name. -/
theorem secret_policy_required (swap : Bool) :
    let r : Recipe 3 := .binary .partialDecrypt (.name names.secretKey) (tallyRecipe [] (0 : Fin 2))
    r.Public names.nonceNames ∧ ¬ r.Public names.restricted ∧
      EqE ((world swap).eval r) (tallyPartial names swap left right [] 0) := by
  refine ⟨⟨show names.secretKey ∉ names.nonceNames by decide,tallyRecipe_public [] 0 _ (by simp)⟩,?_,.refl _⟩
  intro h
  exact (by decide : names.secretKey ∈ names.restricted) |> h.1

end ExplainableCrypto.Helios.Symbolic.TrusteePartialSPOT
