import ExplainableCrypto.Helios.Symbolic.PublicReconstruction

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Representation changes preserve the static-equivalence obligation in both
directions. This does not establish equivalence between different votes. -/
theorem staticEq_iff_representatives (ns : Names n)
    (left right left' right' : CandidateSubstitution n Empty)
    (hl : ∀ j, EqE (left.value j) (left'.value j))
    (hr : ∀ j, EqE (right.value j) (right'.value j)) :
    (frame ns false left right).StaticEq (frame ns true left right) ↔
      (frame ns false left' right').StaticEq (frame ns true left' right') := by
  have hL := Frame.staticEq_of_pointwise (frame_congr ns false left right left' right' hl hr)
  have hR := Frame.staticEq_of_pointwise (frame_congr ns true left right left' right' hl hr)
  exact ⟨fun h => hL.symm.trans (h.trans hR), fun h => hL.trans (h.trans hR.symm)⟩

/-- It suffices to prove the all-recipe static-equivalence theorem on literal
valid bit vectors. The remaining hypothesis includes honest abstention. -/
theorem staticEq_of_bit_candidates (ns : Names n)
    (hbits : ∀ a b : BitCandidate n,
      (frame ns false a.substitution b.substitution).StaticEq (frame ns true a.substitution b.substitution))
    (left right : CandidateSubstitution n Empty) :
    (frame ns false left right).StaticEq (frame ns true left right) := by
  obtain ⟨a, ha⟩ := left.bit_representative
  obtain ⟨b, hb⟩ := right.bit_representative
  exact (staticEq_iff_representatives ns left right a.substitution b.substitution ha hb).mpr (hbits a b)

/-- Given static equivalence, one fully public constructor witness reconstructs
an accepted adversarial ballot in both worlds. Static equivalence remains an
explicit premise until the independent source Lemma 10 obligation is proved. -/
theorem accepted_ballot_common_constructor (ns : Names n)
    (left right : CandidateSubstitution n Empty)
    (hstatic : (frame ns false left right).StaticEq (frame ns true left right))
    (recipe : Recipe 3) (hp : recipe.Public ns.restricted)
    (board : List Ground)
    (ha : Accepted n (publicKey ns) board ((frame ns false left right).eval recipe))
    (hboard : ∀ i : Fin 2, ballot ns i ((choice false left right i).value) ∈ board) :
    ∃ (nonces : Fin (n + 1) → Recipe 3) (bits : Fin (n + 1) → Constant)
      (proofs : Fin (n + 2) → Recipe 3),
      (∀ j, bits j = .zero ∨ bits j = .one) ∧
      CandidateValues (V := Fin 3) (fun j => .const (bits j)) ∧
      (∀ j, (nonces j).Public ns.restricted) ∧
      (∀ j, (proofs j).Public ns.restricted) ∧
      (constructorBallot (.var 0) nonces (fun j => .const (bits j)) proofs).Public ns.restricted ∧
      ∀ swap : Bool, EqE ((frame ns swap left right).eval recipe)
        ((frame ns swap left right).eval (constructorBallot (.var 0) nonces (fun j => .const (bits j)) proofs)) := by
  have hn : ns.nonceNames ⊆ ns.restricted := by
    intro x hx
    exact Finset.mem_union_right _ hx
  obtain ⟨nonces, bits, proofs, hb, hc, hn, hpr, hpub, he⟩ :=
    accepted_ballot_constructor_recipe_of_policy ns false left right ns.restricted hn recipe hp board ha hboard
  refine ⟨nonces, bits, proofs, hb, hc, hn, hpr, hpub, ?_⟩
  intro swap
  cases swap with
  | false => exact he
  | true => exact (hstatic recipe _ hp hpub).mp he

/-- The same literal plaintext vector explains every component in both worlds.
Nonce values may differ across worlds; no same-nonce-value conclusion is used. -/
theorem accepted_ballot_common_components (ns : Names n)
    (left right : CandidateSubstitution n Empty)
    (hstatic : (frame ns false left right).StaticEq (frame ns true left right))
    (recipe : Recipe 3) (hp : recipe.Public ns.restricted)
    (board : List Ground)
    (ha : Accepted n (publicKey ns) board ((frame ns false left right).eval recipe))
    (hboard : ∀ i : Fin 2, ballot ns i ((choice false left right i).value) ∈ board) :
    ∃ (nonces : Fin (n + 1) → Recipe 3) (bits : Fin (n + 1) → Constant),
      (∀ j, bits j = .zero ∨ bits j = .one) ∧
      CandidateValues (V := Fin 3) (fun j => .const (bits j)) ∧
      (∀ j, (nonces j).Public ns.restricted) ∧
      ∀ (swap : Bool) (j : Fin (n + 1)),
        EqE (((frame ns swap left right).eval recipe).project j.val)
          (.ternary .penc (publicKey ns) ((frame ns swap left right).eval (nonces j)) (.const (bits j))) := by
  obtain ⟨nonces, bits, proofs, hb, hc, hn, _, _, he⟩ :=
    accepted_ballot_common_constructor ns left right hstatic recipe hp board ha hboard
  refine ⟨nonces, bits, hb, hc, hn, ?_⟩
  intro swap j
  have hv := (constructorBallot_project_ciphertext (Term.var 0) nonces
    (fun j => Term.const (bits j)) proofs j).subst (frame ns swap left right).value
  apply (EqE.unary .fst ((he swap).drop j.val)).trans
  simpa [Term.subst_project, Term.subst, Frame.eval, frame, Term.project, Term.subst_drop] using hv

end ExplainableCrypto.Helios.Symbolic.Historical.General
