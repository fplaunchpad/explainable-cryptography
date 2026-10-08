import ExplainableCrypto.Helios.Symbolic.HistoricalFrames

namespace ExplainableCrypto.Helios.Symbolic.Historical
variable {n : Nat} {protectedNames : Finset Nat}

theorem Names.nonce_mem (ns : Names n) (i : Fin 2) (j : Fin (n + 1)) : ns.nonce i j ∈ ns.restricted := by
  apply Finset.mem_union.mpr
  exact Or.inr (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)

theorem Names.key_mem (ns : Names n) : ns.secretKey ∈ ns.restricted := by simp [Names.restricted]

theorem ballot_fields_length (ns : Names n) (i : Fin 2) (chosen : Fin (n + 1)) :
    (ballotFields ns i chosen).length = fieldCount n := by
  simp [ballotFields, fieldCount]
  omega

theorem ciphertext_protected (ns : Names n) (i : Fin 2) (chosen j : Fin (n + 1)) :
    (ciphertext ns i chosen j).nonceSafe protectedNames = true := by
  simp [ciphertext, publicKey, vote, Term.nonceSafe]

theorem ballot_fields_protected (ns : Names n) (i : Fin 2) (chosen : Fin (n + 1)) :
    ∀ t ∈ ballotFields ns i chosen, t.nonceSafe protectedNames = true := by
  intro t ht
  simp only [ballotFields, List.mem_append, List.mem_map, List.mem_singleton] at ht
  rcases ht with (⟨j, _, rfl⟩ | ⟨j, _, rfl⟩) | rfl
  · exact ciphertext_protected _ _ _ _
  · rfl
  · rfl

theorem tuple_protected {V : Type} {restricted : Finset Nat} (xs : List (Term V))
    (h : ∀ t ∈ xs, t.nonceSafe restricted = true) : (Term.tuple xs).nonceSafe restricted = true := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [Term.tuple, Term.nonceSafe, Bool.and_eq_true]
    exact ⟨h a (by simp), ih (fun t ht => h t (by simp [ht]))⟩

theorem ballot_protected (ns : Names n) (i : Fin 2) (chosen : Fin (n + 1)) :
    (ballot ns i chosen).nonceSafe protectedNames = true :=
  tuple_protected _ (ballot_fields_protected ns i chosen)

/-- Both assignments protect all handles. The result does not require freshness
or a proof of ballot acceptance; those remain separate source obligations. -/
theorem frame_protected (ns : Names n) (swap : Bool) (left right : Fin (n + 1)) :
    ∀ h, ((frame ns swap left right).value h).nonceSafe protectedNames = true := by
  intro h
  dsimp [frame]
  split_ifs
  · rfl
  · exact ballot_protected _ _ _
  · exact ballot_protected _ _ _

theorem ballot_tail_guard (ns : Names n) (i : Fin 2) (chosen : Fin (n + 1)) :
    TailGuard n (ballot ns i chosen) := by
  have h := drop_tuple (ballotFields ns i chosen)
  rw [ballot_fields_length] at h
  exact h

theorem frame_restricted_name_not_deducible (ns : Names n) (swap : Bool) (left right : Fin (n + 1))
    (r : Recipe 3) (hr : r.Public ns.restricted) {name : Nat} (hn : name ∈ ns.restricted) :
    ¬ EqE ((frame ns swap left right).eval r) (.name name) :=
  (frame ns swap left right).nonce_not_deducible (frame_protected ns swap left right) r hr hn

theorem frame_secret_key_not_deducible (ns : Names n) (swap : Bool) (left right : Fin (n + 1))
    (r : Recipe 3) (hr : r.Public ns.restricted) :
    ¬ EqE ((frame ns swap left right).eval r) (.name ns.secretKey) :=
  frame_restricted_name_not_deducible ns swap left right r hr ns.key_mem

theorem frame_nonce_composition_not_deducible (ns : Names n) (swap : Bool) (left right : Fin (n + 1))
    (r : Recipe 3) (hr : r.Public ns.restricted) (i : Fin 2) (j : Fin (n + 1)) (rest : Ground) :
    ¬ EqE ((frame ns swap left right).eval r) (.binary .compose (.name (ns.nonce i j)) rest) :=
  (frame ns swap left right).nonce_with_remainder_not_deducible
    (frame_protected ns swap left right) r hr (ns.nonce_mem i j) rest

theorem Names.nonce_mem_nonceNames (ns : Names n) (i : Fin 2) (j : Fin (n + 1)) :
    ns.nonce i j ∈ ns.nonceNames :=
  Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩

/-- Lemma 9's nonce-only recipe restriction; literal key/auxiliary names are not
excluded by this premise unless they collide with nonce names. -/
theorem frame_nonce_composition_of_nonce_public (ns : Names n) (swap : Bool)
    (left right : Fin (n + 1)) (r : Recipe 3) (hr : r.Public ns.nonceNames)
    (i : Fin 2) (j : Fin (n + 1)) (rest : Ground) :
    ¬ EqE ((frame ns swap left right).eval r) (.binary .compose (.name (ns.nonce i j)) rest) := by
  apply nonce_safe_not_eqE_name_factor
    (r.nonce_safe_subst (frame ns swap left right).value (hr.nonce_safe r)
      (frame_protected ns swap left right)) (ns.nonce_mem_nonceNames i j)
  simp [Term.composeFactors]

end ExplainableCrypto.Helios.Symbolic.Historical
