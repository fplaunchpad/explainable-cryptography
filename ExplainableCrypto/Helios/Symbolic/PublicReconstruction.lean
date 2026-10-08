import ExplainableCrypto.Helios.Symbolic.GeneralAcceptedReconstruction

namespace ExplainableCrypto.Helios.Symbolic

/-- Removing restrictions preserves publicness. Minimality is not transported. -/
theorem Term.Public.of_subset {V : Type} {small large : Finset Nat}
    {r : Term V} (h : r.Public large) (hsub : small ⊆ large) : r.Public small := by
  induction r with
  | name n => exact fun hn => h (hsub hn)
  | var | const => trivial
  | unary f a ih => exact ih h
  | binary f a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | ternary f a b c iha ihb ihc => exact ⟨iha h.1, ihb h.2.1, ihc h.2.2⟩
  | spk a b c d iha ihb ihc ihd => exact ⟨iha h.1, ihb h.2.1, ihc h.2.2.1, ihd h.2.2.2⟩

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Choose the minimum proof recipe under the caller's policy. The accepted
ballot's nonce-publicness suffices to exclude the remaining aggregate origin. -/
theorem accepted_component_public_nonce_of_policy (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat)
    (hnames : ns.nonceNames ⊆ restricted) (recipe : Recipe 3) (hp : recipe.Public restricted)
    (board : List Ground) (ha : Accepted n (publicKey ns) board ((frame ns swap left right).eval recipe))
    (hboard : ∀ i : Fin 2, ballot ns i ((choice swap left right i).value) ∈ board)
    (v : BallotValues n (publicKey ns) ((frame ns swap left right).eval recipe)) (j : Fin (n + 1)) :
    ∃ r : Recipe 3, r.Public restricted ∧ EqE ((frame ns swap left right).eval r) (v.nonce j) := by
  obtain ⟨z, hz, hez⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value)
    (recipe.project (n + 1 + j.val)) (hp.project _)
  have hez' : EqE ((frame ns swap left right).eval z)
      (((frame ns swap left right).eval recipe).project (n + 1 + j.val)) := by
    simpa only [Frame.eval, Term.subst_project] using hez.symm
  rcases accepted_component_nonce_or_aggregate ns swap left right restricted board _ ha hboard
      j z hz hez' (v.nonce j) (.const (v.bit j)) (v.componentProof j) with hr | ⟨i, hi⟩
  · exact hr
  · subst z
    have hv : EqE ((frame ns swap left right).eval ((Term.var i.succ).project (2 * (n + 1))))
        (aggregateProof ns i ((choice swap left right i).value)) := by
      simpa only [Frame.eval, Term.subst_project, Term.subst, frame_voter_handle] using
        ballot_project_aggregate ns i ((choice swap left right i).value)
    exact False.elim (accepted_component_not_honest_aggregate ns swap left right recipe
      (hp.of_subset hnames) board ha hboard j i (hez'.symm.trans hv))

/-- Lemma 9's reconstruction preserves any caller policy containing the honest
nonces, including the stronger policy needed for static equivalence. -/
theorem accepted_ballot_constructor_recipe_of_policy (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat)
    (hnames : ns.nonceNames ⊆ restricted) (recipe : Recipe 3) (hp : recipe.Public restricted)
    (board : List Ground) (ha : Accepted n (publicKey ns) board ((frame ns swap left right).eval recipe))
    (hboard : ∀ i : Fin 2, ballot ns i ((choice swap left right i).value) ∈ board) :
    ∃ (nonces : Fin (n + 1) → Recipe 3) (bits : Fin (n + 1) → Constant)
      (proofs : Fin (n + 2) → Recipe 3),
      (∀ j, bits j = .zero ∨ bits j = .one) ∧
      CandidateValues (V := Fin 3) (fun j => .const (bits j)) ∧
      (∀ j, (nonces j).Public restricted) ∧
      (∀ j, (proofs j).Public restricted) ∧
      (constructorBallot (.var 0) nonces (fun j => .const (bits j)) proofs).Public restricted ∧
      EqE ((frame ns swap left right).eval recipe)
        ((frame ns swap left right).eval (constructorBallot (.var 0) nonces (fun j => .const (bits j)) proofs)) := by
  obtain ⟨v⟩ := (proofValid_iff_values _ _).mp ha.1
  choose nonces hnonces he using accepted_component_public_nonce_of_policy ns swap left right
    restricted hnames recipe hp board ha hboard v
  let proofs := fun j : Fin (n + 2) => recipe.project (n + 1 + j.val)
  have hproofs : ∀ j, (proofs j).Public restricted := fun j => hp.project _
  refine ⟨nonces, v.bit, proofs, v.isBit, candidate_bits_change_variables v.bit v.candidate,
    hnonces, hproofs, constructorBallot_public _ _ _ _ trivial hnonces (fun _ => trivial) hproofs, ?_⟩
  let fields := constructorFields (Term.var 0) nonces (fun j => .const (v.bit j)) proofs
  change EqE _ ((Term.tuple fields).subst (frame ns swap left right).value)
  rw [Term.subst_tuple]
  have hlen : (fields.map (fun t => t.subst (frame ns swap left right).value)).length = fieldCount n := by
    simp only [List.length_map, fields, constructorFields_length]
  apply tuple_value_from_fields
  · intro i hi
    exact ha.1.pair_tails i (hlen ▸ hi)
  · simpa only [hlen, TailGuard] using ha.2.1
  · intro index hi
    have hidx : index < fieldCount n := hlen ▸ hi
    simp only [List.getElem_map]
    by_cases hc : index < n + 1
    · have hf := constructorFields_ciphertext (Term.var 0) nonces (fun j => .const (v.bit j)) proofs ⟨index, hc⟩
      change EqE _ (((constructorFields (Term.var 0) nonces (fun j => .const (v.bit j)) proofs)[index]'(by rw [constructorFields_length]; exact hidx)).subst _)
      rw [hf]
      exact (v.ciphertext ⟨index, hc⟩).trans
        (.ternary .penc (.refl _) (he ⟨index, hc⟩).symm (.refl _))
    · have hj : index - (n + 1) < n + 2 := by unfold fieldCount at hidx; omega
      have hid : n + 1 + (index - (n + 1)) = index := by omega
      have hf := constructorFields_proof (Term.var 0) nonces (fun j => .const (v.bit j)) proofs ⟨index - (n + 1), hj⟩
      simp only [hid] at hf
      change EqE _ (((constructorFields (Term.var 0) nonces (fun j => .const (v.bit j)) proofs)[index]'(by rw [constructorFields_length]; exact hidx)).subst _)
      rw [hf]
      simp only [proofs, hid, Term.subst_project]
      exact .refl _

end ExplainableCrypto.Helios.Symbolic.Historical.General
