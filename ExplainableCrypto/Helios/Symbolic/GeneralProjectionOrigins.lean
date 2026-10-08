import ExplainableCrypto.Helios.Symbolic.GeneralCandidateProtection
import ExplainableCrypto.Helios.Symbolic.TupleProjectionChains

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

theorem ballot_fields_not_pair (ns : Names n) (i : Fin 2) (chosen : Fin (n + 1) → Ground)
    (t : Ground) (ht : t ∈ ballotFields ns i chosen) (x y : Ground) :
    ¬ EqE t (.binary .pair x y) := by
  simp only [ballotFields, List.mem_append] at ht
  rcases ht with (hc | hp) | ha
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
    exact penc_not_eqE_passive_binary .pair (Or.inl rfl) _ _ _ _ _
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hp
    exact spk_not_eqE_passive_binary .pair (Or.inl rfl) _ _ _ _ _ _
  · have he : t = aggregateProof ns i chosen := by simpa using ha
    subst t
    exact spk_not_eqE_passive_binary .pair (Or.inl rfl) _ _ _ _ _ _

/-- Exact field positions, including all component proofs and the aggregate proof. -/
theorem ballot_field_cases (ns : Names n) (i : Fin 2) (chosen : Fin (n + 1) → Ground)
    (k : Nat) (hk : k < (ballotFields ns i chosen).length) :
    (∃ j : Fin (n + 1), k = j.val ∧ (ballotFields ns i chosen)[k] = ciphertext ns i chosen j) ∨
    (∃ j : Fin (n + 1), k = n + 1 + j.val ∧
      (ballotFields ns i chosen)[k] = componentProof ns i chosen j) ∨
    (k = 2 * (n + 1) ∧ (ballotFields ns i chosen)[k] = aggregateProof ns i chosen) := by
  by_cases hfirst : k < n + 1
  · exact Or.inl ⟨⟨k, hfirst⟩, rfl, by simp [ballotFields, hfirst]⟩
  · by_cases hsecond : k < n + 1 + (n + 1)
    · have hj : k - (n + 1) < n + 1 := by omega
      exact Or.inr (Or.inl ⟨⟨k - (n + 1), hj⟩, by dsimp only; omega,
        by simp [ballotFields, List.getElem_append, hfirst, hj]⟩)
    · have he : k = 2 * (n + 1) := by
        rw [ballot_fields_length, fieldCount] at hk
        omega
      refine Or.inr (Or.inr ⟨he, ?_⟩)
      have hj : ¬ k - (n + 1) < n + 1 := by omega
      have hz : k - (n + 1) - (n + 1) = 0 := by omega
      simp [ballotFields, List.getElem_append, hfirst, hj, hz]

theorem voter_projection_pair_origin (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (i : Fin 2) {recipe : Recipe 3}
    (h : ProjectionChain i.succ recipe) {x y : Ground}
    (he : EqE ((frame ns swap left right).eval recipe) (.binary .pair x y)) :
    ∃ k, k < fieldCount n ∧ recipe = (Term.var i.succ).drop k := by
  have hv : EqE ((frame ns swap left right).value i.succ)
      (Term.tuple (ballotFields ns i ((choice swap left right i).value))) := by
    rw [frame_voter_handle]
    exact .refl _
  obtain ⟨k, hk, hr⟩ := h.pair_origin _ hv (ballot_fields_not_pair ns i _) he
  exact ⟨k, by simpa only [ballot_fields_length] using hk, hr⟩

/-- Every ciphertext-valued chain on a ballot is exactly one honest component selector. -/
theorem voter_projection_ciphertext_origin (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (i : Fin 2) {recipe : Recipe 3}
    (h : ProjectionChain i.succ recipe) {k s m : Ground}
    (he : EqE ((frame ns swap left right).eval recipe) (.ternary .penc k s m)) :
    ∃ j : Fin (n + 1), recipe = (Term.var i.succ).project j.val ∧
      EqE (ciphertext ns i ((choice swap left right i).value) j) (.ternary .penc k s m) := by
  have hv : EqE ((frame ns swap left right).value i.succ)
      (Term.tuple (ballotFields ns i ((choice swap left right i).value))) := by
    rw [frame_voter_handle]
    exact .refl _
  obtain ⟨idx, hi, hr, hval⟩ := h.ciphertext_origin _ hv (ballot_fields_not_pair ns i _) he
  rcases ballot_field_cases ns i ((choice swap left right i).value) idx hi with
    ⟨j, rfl, hfield⟩ | ⟨j, _, hfield⟩ | ⟨_, hfield⟩
  · exact ⟨j, hr, hfield ▸ hval⟩
  · rw [hfield] at hval
    exact False.elim (penc_not_eqE_spk _ _ _ _ _ _ _ hval.symm)
  · rw [hfield] at hval
    exact False.elim (penc_not_eqE_spk _ _ _ _ _ _ _ hval.symm)

/-- Proof-valued ballot chains select a component proof or the aggregate position. -/
theorem voter_projection_proof_origin (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (i : Fin 2) {recipe : Recipe 3}
    (h : ProjectionChain i.succ recipe) {k s m c : Ground}
    (he : EqE ((frame ns swap left right).eval recipe) (.spk k s m c)) :
    (∃ j : Fin (n + 1), recipe = (Term.var i.succ).project (n + 1 + j.val) ∧
      EqE (componentProof ns i ((choice swap left right i).value) j) (.spk k s m c)) ∨
    (recipe = (Term.var i.succ).project (2 * (n + 1)) ∧
      EqE (aggregateProof ns i ((choice swap left right i).value)) (.spk k s m c)) := by
  have hv : EqE ((frame ns swap left right).value i.succ)
      (Term.tuple (ballotFields ns i ((choice swap left right i).value))) := by
    rw [frame_voter_handle]
    exact .refl _
  obtain ⟨idx, hi, hr, hval⟩ := h.proof_origin _ hv (ballot_fields_not_pair ns i _) he
  rcases ballot_field_cases ns i ((choice swap left right i).value) idx hi with
    ⟨j, _, hfield⟩ | ⟨j, rfl, hfield⟩ | ⟨rfl, hfield⟩
  · rw [hfield] at hval
    exact False.elim (penc_not_eqE_spk _ _ _ _ _ _ _ hval)
  · exact Or.inl ⟨j, hr, hfield ▸ hval⟩
  · exact Or.inr ⟨hr, hfield ▸ hval⟩

theorem key_projection_chain_not_ciphertext (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) {recipe : Recipe 3} (h : ProjectionChain 0 recipe)
    (k s m : Ground) :
    ¬ EqE ((frame ns swap left right).eval recipe) (.ternary .penc k s m) :=
  h.not_ciphertext_of_handle (σ := (frame ns swap left right).value)
    (fun _ _ => pk_not_eqE_pair _ _ _) (fun _ _ _ => pk_not_eqE_penc _ _ _ _) k s m

/-- Covers all three initial handles, both swaps and every positive candidate count. -/
theorem frame_projection_ciphertext_origin (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (v : Fin 3) {recipe : Recipe 3} (h : ProjectionChain v recipe)
    {k s m : Ground} (he : EqE ((frame ns swap left right).eval recipe) (.ternary .penc k s m)) :
    ∃ i : Fin 2, ∃ j : Fin (n + 1), v = i.succ ∧
      recipe = (Term.var i.succ).project j.val ∧
      EqE (ciphertext ns i ((choice swap left right i).value) j) (.ternary .penc k s m) := by
  fin_cases v
  · exact False.elim (key_projection_chain_not_ciphertext ns swap left right h k s m he)
  · obtain ⟨j, hr, hv⟩ := voter_projection_ciphertext_origin ns swap left right 0 h he
    exact ⟨0, j, rfl, hr, hv⟩
  · obtain ⟨j, hr, hv⟩ := voter_projection_ciphertext_origin ns swap left right 1 h he
    exact ⟨1, j, rfl, hr, hv⟩


private theorem ballot_pair_shape (ns : Names n) (i : Fin 2) (values : Fin (n + 1) → Ground) :
    ∃ a b, ballot ns i values = .binary .pair a b := by
  have hl := ballot_fields_length ns i values
  cases he : ballotFields ns i values with
  | nil => simp only [he, List.length_nil, fieldCount] at hl; omega
  | cons a xs => exact ⟨a, Term.tuple xs, by simp [ballot, he, Term.tuple]⟩

theorem frame_handle_not_ciphertext (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (v : Fin 3) (k r m : Ground) :
    ¬ EqE ((frame ns swap left right).value v) (.ternary .penc k r m) := by
  fin_cases v
  · exact pk_not_eqE_penc _ _ _ _
  · obtain ⟨a, b, hb⟩ := ballot_pair_shape ns 0 (choice swap left right 0).value
    change ¬ EqE (ballot ns 0 (choice swap left right 0).value) _
    rw [hb]
    exact fun h => penc_not_eqE_passive_binary .pair (Or.inl rfl) k r m a b h.symm
  · obtain ⟨a, b, hb⟩ := ballot_pair_shape ns 1 (choice swap left right 1).value
    change ¬ EqE (ballot ns 1 (choice swap left right 1).value) _
    rw [hb]
    exact fun h => penc_not_eqE_passive_binary .pair (Or.inl rfl) k r m a b h.symm

/-- Literal constant plaintext certificates follow from E-bit values; the raw
honest plaintext need not be a constant constructor. -/
theorem honest_projection_certificate (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (i : Fin 2) (j : Fin (n + 1)) :
    ∃ bit : Constant, (bit = .zero ∨ bit = .one) ∧
      CiphertextProduct (frame ns swap left right).value (publicKey ns)
        ((Term.var i.succ : Recipe 3).project j.val) (.const bit) (.name (ns.nonce i j)) := by
  have he : EqE ((frame ns swap left right).eval ((Term.var i.succ).project j.val))
      (ciphertext ns i (choice swap left right i).value j) := by
    simpa only [Frame.eval, Term.subst_project, Term.subst, frame_voter_handle] using
      ballot_project_ciphertext ns i (choice swap left right i).value j
  have hs : 1 < ((Term.var i.succ : Recipe 3).project j.val).nodeCount := by
    have hpos := ((Term.var i.succ : Recipe 3).drop j.val).nodeCount_pos
    simp only [Term.project, Term.nodeCount]
    omega
  rcases (choice swap left right i).valid.component_bit j with hz | ho
  · exact ⟨.zero, Or.inl rfl, .constant _ _ _
      (he.trans (.ternary .penc (.refl _) (.refl _) hz)) hs⟩
  · exact ⟨.one, Or.inr rfl, .constant _ _ _
      (he.trans (.ternary .penc (.refl _) (.refl _) ho)) hs⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General
