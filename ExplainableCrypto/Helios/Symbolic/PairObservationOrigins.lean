import ExplainableCrypto.Helios.Symbolic.PartialDecryptionObservationInduction

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Full-E equality of finite tuples preserves their number of pair cells,
even when fields reduce or themselves contain pairs. -/
theorem EqE.tuple_length {xs ys : List (Term V)} (he : EqE (Term.tuple xs) (Term.tuple ys)) :
    xs.length = ys.length := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => have h := tuple_eqE_pair_nonempty [] he; simp at h
  | cons x xs ih =>
    cases ys with
    | nil => have h := tuple_eqE_pair_nonempty [] he.symm; simp at h
    | cons y ys =>
      have h := ih ((EqE.pair_iff _ _ _ _).mp he).2
      simpa only [List.length_cons] using congrArg Nat.succ h

/-- The same in-range position in E-equal tuples has E-equal fields. -/
theorem EqE.tuple_get {xs ys : List (Term V)} (he : EqE (Term.tuple xs) (Term.tuple ys))
    (j : Nat) (hx : j < xs.length) (hy : j < ys.length) : EqE xs[j] ys[j] :=
  (project_tuple_get xs j hx).symm.trans
    ((EqE.unary .fst (he.drop j)).trans (project_tuple_get ys j hy))

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Exact nonempty ballot-tail syntax, alongside freely constructed pairs. -/
def PairObservationForm (n : Nat) (r : Recipe 3) : Prop :=
  (∃ a b, r = .binary .pair a b) ∨
    ∃ i : Fin 2, ∃ k, k < fieldCount n ∧ r = (Term.var i.succ).drop k

theorem ballot_tail_recipe_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (i : Fin 2) (k : Nat) (hk : k ≤ fieldCount n) :
    EqE ((frame ns swap left right).eval ((Term.var i.succ).drop k))
      (Term.tuple ((ballotFields ns i (choice swap left right i).value).drop k)) := by
  simpa only [Frame.eval, Term.subst_drop, Term.subst, frame_voter_handle, ballot] using
    (tuple_drop_reduces (ballotFields ns i (choice swap left right i).value) k
      (by simpa only [ballot_fields_length] using hk)).sound

theorem ballot_tail_pair_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (i : Fin 2) (k : Nat) (hk : k < fieldCount n) :
    ∃ a b, EqE ((frame ns swap left right).eval ((Term.var i.succ).drop k)) (.binary .pair a b) := by
  have hv := ballot_tail_recipe_value ns swap left right i k (by omega)
  have hl : 0 < ((ballotFields ns i (choice swap left right i).value).drop k).length := by
    simp only [List.length_drop, ballot_fields_length]; omega
  cases he : (ballotFields ns i (choice swap left right i).value).drop k with
  | nil => simp only [he, List.length_nil] at hl; omega
  | cons a xs => exact ⟨a, Term.tuple xs, by simpa only [he, Term.tuple] using hv⟩

/-- A pair-valued handle chain is a nonempty tail of one of the two ballots. -/
theorem frame_projection_pair_origin (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (v : Fin 3) {r : Recipe 3}
    (hc : ProjectionChain v r) {a b : Ground}
    (he : EqE ((frame ns swap left right).eval r) (.binary .pair a b)) :
    ∃ i : Fin 2, ∃ k, k < fieldCount n ∧ r = (Term.var i.succ).drop k := by
  fin_cases v
  · exact False.elim (hc.not_pair_of_handle (σ := (frame ns swap left right).value)
      (fun _ _ => pk_not_eqE_pair _ _ _) a b he)
  · obtain ⟨k, hk, hr⟩ := voter_projection_pair_origin ns swap left right 0 hc he
    exact ⟨0, k, hk, hr⟩
  · obtain ⟨k, hk, hr⟩ := voter_projection_pair_origin ns swap left right 1 hc he
    exact ⟨1, k, hk, hr⟩

theorem minimum_pair_observation_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value r) {a b : Ground}
    (he : EqE ((frame ns swap left right).eval r) (.binary .pair a b)) :
    PairObservationForm n r := by
  rcases minimum_pair_origin ns swap left right restricted r hm he with hp | ⟨v, hc⟩
  · exact Or.inl hp
  · exact Or.inr (frame_projection_pair_origin ns swap left right v hc he)

/-- Pair-valuedness of the classified syntax holds in either swapped world,
without transporting arbitrary evaluations or minimum size. -/
theorem PairObservationForm.pair_value {r : Recipe 3} (h : PairObservationForm n r)
    (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty) :
    ∃ a b, EqE ((frame ns swap left right).eval r) (.binary .pair a b) := by
  rcases h with ⟨a, b, rfl⟩ | ⟨i, k, hk, rfl⟩
  · exact ⟨_, _, .refl _⟩
  · exact ballot_tail_pair_value ns swap left right i k hk

private theorem last_ballot_field (ns : Names n) (i : Fin 2) (chosen : Fin (n + 1) → Ground) :
    (ballotFields ns i chosen)[2 * (n + 1)]'(
      by rw [ballot_fields_length]; unfold fieldCount; omega) = aggregateProof ns i chosen := by
  simp [ballotFields, List.getElem_append, show ¬ 2 * (n + 1) < n + 1 by omega,
    show 2 * (n + 1) - (n + 1) = n + 1 by omega]

/-- Nonempty tails retain their length and aggregate-proof nonce provenance.
Empty tails are deliberately excluded: both voters' empty tails are bottom. -/
theorem ballot_tail_equality_iff (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (i j : Fin 2) (k l : Nat)
    (hk : k < fieldCount n) (hl : l < fieldCount n) :
    EqE ((frame ns swap left right).eval ((Term.var i.succ).drop k))
      ((frame ns swap left right).eval ((Term.var j.succ).drop l)) ↔ i = j ∧ k = l := by
  constructor
  · intro he
    have ht := (ballot_tail_recipe_value ns swap left right i k (by omega)).symm.trans
      (he.trans (ballot_tail_recipe_value ns swap left right j l (by omega)))
    have hlen := ht.tuple_length
    simp only [List.length_drop, ballot_fields_length] at hlen
    have hkl : k = l := by omega
    subst l
    have hlast := ht.tuple_get (2 * (n + 1) - k)
      (by simp only [List.length_drop, ballot_fields_length]; unfold fieldCount at *; omega)
      (by simp only [List.length_drop, ballot_fields_length]; unfold fieldCount at *; omega)
    have hidx : k + (2 * (n + 1) - k) = 2 * (n + 1) := by unfold fieldCount at hk; omega
    simp only [List.getElem_drop, hidx, last_ballot_field] at hlast
    exact ⟨(aggregate_proof_equality_iff ns hf swap left right i j).mp hlast, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .refl _

end ExplainableCrypto.Helios.Symbolic.Historical.General
