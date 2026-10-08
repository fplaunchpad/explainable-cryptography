import ExplainableCrypto.Helios.Symbolic.GeneralStaticTransfer
import ExplainableCrypto.Helios.Symbolic.StaticAcceptance
import ExplainableCrypto.Helios.Symbolic.GeneralCandidateSPOT
import ExplainableCrypto.Helios.Symbolic.RawNormalization

namespace ExplainableCrypto.Helios.Symbolic.StaticEquivalenceSPOT
open Historical

abbrev collisionNames : Names 1 := ⟨10, 11, fun _ _ => 20⟩
abbrev zeroVote : CandidateSubstitution 1 Empty := (BitCandidate.abstain 1).substitution
abbrev firstVote : CandidateSubstitution 1 Empty := (BitCandidate.selected (0 : Fin 2)).substitution
abbrev first : Recipe 3 := (Term.var 1).project 0
abbrev second : Recipe 3 := (Term.var 1).project 1

private theorem eval_cipher {n : Nat} (ns : Names n) (swap : Bool)
    (a b : CandidateSubstitution n Empty) (i : Fin 2) (j : Fin (n + 1)) :
    EqE ((General.frame ns swap a b).eval ((Term.var i.succ).project j.val))
      (General.ciphertext ns i (General.choice swap a b i).value j) := by
  simpa only [Frame.eval, Term.subst_project, Term.subst, General.frame_voter_handle] using
    General.ballot_project_ciphertext ns i (General.choice swap a b i).value j

theorem collision_names_not_fresh : ¬ collisionNames.Fresh := by
  unfold Names.Fresh Function.Injective
  decide

/-- Equal randomness exposes equality of hidden bits through ciphertext equality. -/
theorem collision_distinguishes :
    EqE ((General.frame collisionNames false zeroVote firstVote).eval first)
      ((General.frame collisionNames false zeroVote firstVote).eval second) ∧
    ¬ EqE ((General.frame collisionNames true zeroVote firstVote).eval first)
      ((General.frame collisionNames true zeroVote firstVote).eval second) := by
  constructor
  · exact (eval_cipher collisionNames false zeroVote firstVote 0 0).trans
      (eval_cipher collisionNames false zeroVote firstVote 0 1).symm
  · intro he
    have hc := (eval_cipher collisionNames true zeroVote firstVote 0 0).symm.trans
      (he.trans (eval_cipher collisionNames true zeroVote firstVote 0 1))
    exact zero_not_one ((EqE.penc_iff _ _ _ _ _ _).mp hc).2.2.symm

theorem freshness_required_for_staticEq :
    ¬ (General.frame collisionNames false zeroVote firstVote).StaticEq
      (General.frame collisionNames true zeroVote firstVote) := by
  intro hs
  exact collision_distinguishes.2 ((hs first second (by trivial) (by trivial)).mp collision_distinguishes.1)

/-- With fresh names, the same equality probe is false in both worlds, even
though the first voter's plaintext equality changes. -/
theorem fresh_ciphertext_probe (swap : Bool) :
    ¬ EqE ((General.frame HistoricalFrameSPOT.names swap zeroVote firstVote).eval first)
      ((General.frame HistoricalFrameSPOT.names swap zeroVote firstVote).eval second) := by
  intro he
  have hc := (eval_cipher HistoricalFrameSPOT.names swap zeroVote firstVote 0 0).symm.trans
    (he.trans (eval_cipher HistoricalFrameSPOT.names swap zeroVote firstVote 0 1))
  have hn := (EqE.name_iff _ _).mp ((EqE.penc_iff _ _ _ _ _ _).mp hc).2.1
  change 20 = 21 at hn
  omega

/-- Honest checking really succeeds in both worlds; observations are not all stuck. -/
theorem honest_component_check (swap : Bool) :
    EqE ((General.frame HistoricalFrameSPOT.names swap zeroVote firstVote).eval
      (.ternary .checkspk (.var 0) first ((Term.var 1).project 2))) (.const .ok) := by
  have h := (General.honest_proofs_valid HistoricalFrameSPOT.names 0
    (General.choice swap zeroVote firstVote 0).value (General.choice swap zeroVote firstVote 0).valid).2 (0 : Fin 2)
  simpa [Frame.eval, first, Term.subst, Term.subst_project, General.frame_voter_handle,
    General.frame] using h

/-- Raw observation testing misses the E0-enabled aggregate check. -/
theorem raw_aggregate_observer_incomplete :
    let φ := General.frame HistoricalFrameSPOT.names false zeroVote firstVote
    let r : Recipe 3 := .ternary .checkspk (.var 0) (aggregateCiphertext 1 (.var 1))
      ((Term.var 1).project 4)
    EqE (φ.eval r) (.const .ok) ∧ normalizeRaw (φ.eval r) ≠ .const .ok := by
  dsimp only
  constructor
  · have h := (General.honest_proofs_valid HistoricalFrameSPOT.names 0 zeroVote.value zeroVote.valid).1
    simpa [Frame.eval, Term.subst, aggregateCiphertext_subst, Term.subst_project, General.frame,
      General.choice] using h
  · decide

abbrev singleNames : Names 0 := BallotValueSPOT.names
abbrev singleZero : CandidateSubstitution 0 Empty := (BitCandidate.abstain 0).substitution
abbrev singleOne : CandidateSubstitution 0 Empty := (BitCandidate.selected (0 : Fin 1)).substitution
abbrev decryptFirst : Recipe 3 := .binary .dec (.name 10) ((Term.var 1).project 0)

private theorem decrypt_value (swap : Bool) :
    EqE ((General.frame singleNames swap singleZero singleOne).eval decryptFirst)
      (.const (if swap then .one else .zero)) := by
  have hc := eval_cipher singleNames swap singleZero singleOne 0 0
  cases swap <;> exact (EqE.binary .dec (.refl _) hc).trans (.equation (.decrypt _ _ _))

/-- The full policy forbids a key recipe that the nonce-only policy permits. -/
theorem full_policy_required : decryptFirst.Public singleNames.nonceNames ∧
    ¬ decryptFirst.Public singleNames.restricted ∧
    ¬ Frame.StaticEq (restricted := singleNames.nonceNames)
      ⟨(General.frame singleNames false singleZero singleOne).value⟩
      ⟨(General.frame singleNames true singleZero singleOne).value⟩ := by
  have hp : decryptFirst.Public singleNames.nonceNames := by change 10 ∉ singleNames.nonceNames ∧ True; decide
  refine ⟨hp, ?_, ?_⟩
  · change ¬ (10 ∉ singleNames.restricted ∧ True)
    decide
  · intro hs
    have he := (hs decryptFirst (.const .zero) hp trivial).mp (decrypt_value false)
    exact zero_not_one (he.symm.trans (decrypt_value true))

/-- An all-recipe positive instance changes reducible vote representations,
not the vote itself. It does not discharge the swap theorem. -/
theorem representative_frames_staticEq (swap : Bool) :
    (General.frame GeneralCandidateSPOT.names swap GeneralCandidateSPOT.represented GeneralCandidateSPOT.abstain).StaticEq
      (General.frame GeneralCandidateSPOT.names swap GeneralCandidateSPOT.selected GeneralCandidateSPOT.abstain) := by
  apply Frame.staticEq_of_pointwise
  intro i
  exact GeneralCandidateSPOT.representative_recipe_values swap (.var i)

end ExplainableCrypto.Helios.Symbolic.StaticEquivalenceSPOT
