import ExplainableCrypto.Helios.Symbolic.GeneralAggregateExclusion

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Source Lemma 9 with all valid ground candidate substitutions, including
honest abstention and arbitrary E-equivalent representatives. The corrected
tail guard, nonce-only publicness and both honest board members remain explicit. -/
theorem accepted_ballot_constructor_recipe (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (recipe : Recipe 3) (hp : recipe.Public ns.nonceNames)
    (board : List Ground) (ha : Accepted n (publicKey ns) board ((frame ns swap left right).eval recipe))
    (hboard : ∀ i : Fin 2, ballot ns i ((choice swap left right i).value) ∈ board) :
    ∃ (nonces : Fin (n + 1) → Recipe 3) (bits : Fin (n + 1) → Constant)
      (proofs : Fin (n + 2) → Recipe 3),
      (∀ j, bits j = .zero ∨ bits j = .one) ∧
      CandidateValues (V := Fin 3) (fun j => .const (bits j)) ∧
      (∀ j, (nonces j).Public ns.nonceNames) ∧
      (∀ j, (proofs j).Public ns.nonceNames) ∧
      (constructorBallot (.var 0) nonces (fun j => .const (bits j)) proofs).Public ns.nonceNames ∧
      EqE ((frame ns swap left right).eval recipe)
        ((frame ns swap left right).eval (constructorBallot (.var 0) nonces (fun j => .const (bits j)) proofs)) := by
  obtain ⟨v⟩ := (proofValid_iff_values _ _).mp ha.1
  choose nonces hnonces he using accepted_component_public_nonce ns swap left right recipe hp board ha hboard v
  let proofs := fun j : Fin (n + 2) => recipe.project (n + 1 + j.val)
  have hproofs : ∀ j, (proofs j).Public ns.nonceNames := fun j => hp.project _
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
