import ExplainableCrypto.Helios.Symbolic.HistoricalAggregation
import ExplainableCrypto.Helios.Symbolic.FullStructure

namespace ExplainableCrypto.Helios.Symbolic.Historical
variable {n : Nat}

theorem ballot_project_ciphertext (ns : Names n) (i : Fin 2) (chosen j : Fin (n + 1)) :
    EqE ((ballot ns i chosen).project j.val) (ciphertext ns i chosen j) := by
  have hb : j.val < (ballotFields ns i chosen).length := by
    rw [ballot_fields_length, fieldCount]
    omega
  have h := project_tuple_get (ballotFields ns i chosen) j.val hb
  simpa [ballot, ballotFields, List.getElem_append, j.isLt] using h

theorem ballot_project_proof (ns : Names n) (i : Fin 2) (chosen j : Fin (n + 1)) :
    EqE ((ballot ns i chosen).project (n + 1 + j.val)) (componentProof ns i chosen j) := by
  have hb : n + 1 + j.val < (ballotFields ns i chosen).length := by
    rw [ballot_fields_length, fieldCount]
    omega
  have h := project_tuple_get (ballotFields ns i chosen) (n + 1 + j.val) hb
  have h₁ : ¬ n + 1 + j.val < n + 1 := by omega
  have h₂ : n + 1 + j.val < n + 1 + (n + 1) := by omega
  simpa [ballot, ballotFields, List.getElem_append, h₁, h₂] using h

theorem ballot_project_aggregate (ns : Names n) (i : Fin 2) (chosen : Fin (n + 1)) :
    EqE ((ballot ns i chosen).project (2 * (n + 1))) (aggregateProof ns i chosen) := by
  have hb : 2 * (n + 1) < (ballotFields ns i chosen).length := by
    rw [ballot_fields_length, fieldCount]
    omega
  have h := project_tuple_get (ballotFields ns i chosen) (2 * (n + 1)) hb
  have he : 2 * (n + 1) = n + 1 + (n + 1) := by omega
  simpa [ballot, ballotFields, List.getElem_append, he] using h

private theorem foldl_congr {α : Type} (xs : List α) (f : Binary) (a b : Ground)
    (left right : α → Ground) (h : EqE a b) (hx : ∀ j ∈ xs, EqE (left j) (right j)) :
    EqE (xs.foldl (fun acc j => .binary f acc (left j)) a)
      (xs.foldl (fun acc j => .binary f acc (right j)) b) := by
  induction xs generalizing a b with
  | nil => exact h
  | cons j xs ih =>
    exact ih _ _ (.binary f h (hx j (by simp))) (fun k hk => hx k (by simp [hk]))

theorem ballot_aggregate_ciphertext (ns : Names n) (i : Fin 2) (chosen : Fin (n + 1)) :
    EqE (aggregateCiphertext n (ballot ns i chosen)) (foldCandidates .mul (ciphertext ns i chosen)) := by
  apply foldl_congr
  · exact ballot_project_ciphertext ns i chosen 0
  · intro j _
    exact ballot_project_ciphertext ns i chosen j.succ

theorem honest_proofs_valid (ns : Names n) (i : Fin 2) (chosen : Fin (n + 1)) :
    ProofValid n (publicKey ns) (ballot ns i chosen) := by
  have hc := (ballot_aggregate_ciphertext ns i chosen).trans (ciphertext_product ns i chosen)
  have hp : EqE (aggregateProof ns i chosen)
      (.spk (publicKey ns) (foldCandidates .compose (fun j => .name (ns.nonce i j))) (.const .one)
        (.ternary .penc (publicKey ns) (foldCandidates .compose (fun j => .name (ns.nonce i j))) (.const .one))) :=
    .spk (.refl _) (.refl _) (vote_sum_one chosen).sound (ciphertext_product ns i chosen)
  constructor
  · exact (EqE.ternary .checkspk (.refl _) hc ((ballot_project_aggregate ns i chosen).trans hp)).trans
      (RootStep.check_one (publicKey ns) (foldCandidates .compose (fun j => .name (ns.nonce i j)))).to_modulo.sound
  · intro j
    have he := EqE.ternary .checkspk (.refl (publicKey ns))
      (ballot_project_ciphertext ns i chosen j) (ballot_project_proof ns i chosen j)
    by_cases hj : j = chosen
    · exact he.trans (by simpa [ciphertext, componentProof, vote, hj] using
        (RootStep.check_one (publicKey ns) (.name (ns.nonce i j))).to_modulo.sound)
    · exact he.trans (by simpa [ciphertext, componentProof, vote, hj] using
        (RootStep.check_zero (publicKey ns) (.name (ns.nonce i j))).to_modulo.sound)

theorem honest_empty_board_accepts (ns : Names n) (i : Fin 2) (chosen : Fin (n + 1)) :
    Accepted n (publicKey ns) [] (ballot ns i chosen) := by
  refine ⟨honest_proofs_valid ns i chosen, ballot_tail_guard ns i chosen, ?_⟩
  intro earlier h
  simp at h

theorem fresh_voters_no_reuse (ns : Names n) (hf : ns.Fresh) (i j : Fin 2) (hne : i ≠ j)
    (chosen chosen' : Fin (n + 1)) : NoReuse n [ballot ns i chosen] (ballot ns j chosen') := by
  intro earlier hm a b he
  have hm' : earlier = ballot ns i chosen := by simpa using hm
  subst earlier
  have hc := (ballot_project_ciphertext ns i chosen a).symm.trans
    (he.trans (ballot_project_ciphertext ns j chosen' b))
  have hr := ((EqE.penc_iff _ _ _ _ _ _).mp hc).2.1
  have hn := (EqE.name_iff _ _).mp hr
  have hp : (i, a) = (j, b) := hf.2.1 hn
  exact hne (congrArg Prod.fst hp)

theorem honest_accepts_after_other (ns : Names n) (hf : ns.Fresh) (i j : Fin 2) (hne : i ≠ j)
    (chosen chosen' : Fin (n + 1)) :
    Accepted n (publicKey ns) [ballot ns i chosen] (ballot ns j chosen') :=
  ⟨honest_proofs_valid ns j chosen', ballot_tail_guard ns j chosen',
    fresh_voters_no_reuse ns hf i j hne chosen chosen'⟩

end ExplainableCrypto.Helios.Symbolic.Historical
