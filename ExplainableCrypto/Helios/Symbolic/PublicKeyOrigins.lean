import ExplainableCrypto.Helios.Symbolic.ProofObservationInduction

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type}

theorem pk_not_eqE_passive_binary (f : Binary) (hf : f = .pair ∨ f = .partialDecrypt)
    (k a b : Term V) : ¬ EqE (.unary .pk k) (.binary f a b) := by
  intro he
  obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp he
  obtain ⟨_, hk, _⟩ := hl.pk_components
  obtain ⟨_, _, hb, _⟩ := hr.passive_binary_components hf
  rcases hf with rfl | rfl <;> cases (hk.symm.trans hb).head_eq

/-- A key-valued projection must reach a pair and select a key-valued member;
the original argument need not have a literal pair head. -/
theorem EqE.projection_pk_inversion {f : Unary} (hf : f = .fst ∨ f = .snd)
    {a k : Term V} (he : EqE (.unary f a) (.unary .pk k)) :
    ∃ x y, ReducesModulo a (.binary .pair x y) ∧ EqE (if f = .fst then x else y) (.unary .pk k) := by
  obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp he
  rcases hl.projection_cases hf with ⟨_, _, ht⟩ | ⟨x, y, hp, hout⟩
  · obtain ⟨_, hk, _⟩ := hr.pk_components
    rcases hf with rfl | rfl <;> cases (ht.symm.trans hk).head_eq
  · exact ⟨x, y, hp, hout.sound.trans hr.sound.symm⟩

/-- Key-valued decryption must reach an actual E5/E6 match. -/
theorem EqE.decryption_pk_inversion {a b k : Term V}
    (he : EqE (.binary .dec a b) (.unary .pk k)) :
    ∃ p, DecryptionMatch a b p ∧ EqE p (.unary .pk k) := by
  obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp he
  rcases hl.decryption_cases with ⟨_, _, _, _, ht⟩ | ⟨p, hp, hout⟩
  · obtain ⟨_, hk, _⟩ := hr.pk_components
    cases (ht.symm.trans hk).head_eq
  · exact ⟨p, hp, hout.sound.trans hr.sound.symm⟩

theorem tuple_not_eqE_pk (xs : List (Term V)) (k : Term V) :
    ¬ EqE (Term.tuple xs) (.unary .pk k) := by
  cases xs with
  | nil =>
    intro he
    obtain ⟨_, hshape, _⟩ := he.symm.pk_irreducible_shape (constant_irreducible .bottom)
    cases hshape
  | cons a xs => exact fun he => pk_not_eqE_pair _ _ _ he.symm

/-- A tuple with non-pair, non-key fields exposes no public key through any
fst/snd chain. This includes complete and exhausted suffix tuples. -/
theorem ProjectionChain.not_pk_of_tuple {σ : V → Term W} {v : V} {r : Term V}
    (hc : ProjectionChain v r) (xs : List (Term W)) (hv : EqE (σ v) (Term.tuple xs))
    (hp : ∀ t ∈ xs, ∀ x y, ¬ EqE t (.binary .pair x y))
    (hk : ∀ t ∈ xs, ∀ k, ¬ EqE t (.unary .pk k)) (k : Term W) :
    ¬ EqE (r.subst σ) (.unary .pk k) := by
  intro he
  cases hc with
  | handle => exact tuple_not_eqE_pk xs k (hv.symm.trans he)
  | step f hf hc =>
    obtain ⟨x, y, hpair, _⟩ := he.projection_pk_inversion hf
    obtain ⟨i, hi, rfl⟩ := hc.pair_origin xs hv hp hpair.sound
    rcases hf with rfl | rfl
    · have hs : EqE (((Term.var v : Term V).project i).subst σ) xs[i] := by
        rw [Term.subst_project]
        exact (EqE.unary .fst (hv.drop i)).trans (project_tuple_get xs i hi)
      exact hk xs[i] (List.getElem_mem hi) k (hs.symm.trans he)
    · have hs : EqE ((Term.unary .snd ((Term.var v).drop i) : Term V).subst σ)
          (Term.tuple (xs.drop (i + 1))) := by
        rw [← Term.drop_succ_outer, Term.subst_drop]
        exact (hv.drop (i + 1)).trans (tuple_drop_reduces xs (i + 1) (by omega)).sound
      exact tuple_not_eqE_pk _ k (hs.symm.trans he)

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

theorem ballot_fields_not_pk (ns : Names n) (i : Fin 2) (chosen : Fin (n + 1) → Ground)
    (t : Ground) (ht : t ∈ ballotFields ns i chosen) (k : Ground) : ¬ EqE t (.unary .pk k) := by
  simp only [ballotFields, List.mem_append, List.mem_map, List.mem_singleton] at ht
  rcases ht with (⟨j, _, rfl⟩ | ⟨j, _, rfl⟩) | rfl
  · exact fun he => pk_not_eqE_penc _ _ _ _ he.symm
  · exact fun he => pk_not_eqE_spk _ _ _ _ _ he.symm
  · exact fun he => pk_not_eqE_spk _ _ _ _ _ he.symm

theorem voter_projection_not_pk (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (i : Fin 2) {r : Recipe 3}
    (hc : ProjectionChain i.succ r) (k : Ground) :
    ¬ EqE ((frame ns swap left right).eval r) (.unary .pk k) := by
  have hv : EqE ((frame ns swap left right).value i.succ)
      (Term.tuple (ballotFields ns i (choice swap left right i).value)) := by
    rw [frame_voter_handle]
    exact .refl _
  exact hc.not_pk_of_tuple _ hv (ballot_fields_not_pair ns i _) (ballot_fields_not_pk ns i _) k

/-- The only key-valued projection chain is the published election-key handle
itself, across all three handles and arbitrary valid candidate representatives. -/
theorem frame_projection_pk_origin (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (v : Fin 3) {r : Recipe 3}
    (hc : ProjectionChain v r) {k : Ground}
    (he : EqE ((frame ns swap left right).eval r) (.unary .pk k)) : r = .var 0 := by
  fin_cases v
  · cases hc with
    | handle => rfl
    | step f hf hc =>
      obtain ⟨x, y, hp, _⟩ := he.projection_pk_inversion hf
      exact False.elim (hc.not_pair_of_handle (σ := (frame ns swap left right).value)
        (fun _ _ => pk_not_eqE_pair _ _ _) x y hp.sound)
  · exact False.elim (voter_projection_not_pk ns swap left right 0 hc k he)
  · exact False.elim (voter_projection_not_pk ns swap left right 1 hc k he)

end ExplainableCrypto.Helios.Symbolic.Historical.General
