import ExplainableCrypto.Helios.Symbolic.PublicKeyObservationInduction

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type}

/-- Normal E-values of either passive binary constructor retain the constructor
and both ordered components. Normality is required only of the supplied target. -/
theorem EqE.passive_binary_irreducible_shape {f : Binary} (hf : f = .pair ∨ f = .partialDecrypt)
    {a b t : Term V} (he : EqE (.binary f a b) t) (ht : Irreducible t) :
    ∃ x y, t = .binary f x y ∧ EqE a x ∧ EqE b y := by
  obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp he
  obtain ⟨a₁, b₁, hw, ha, hb⟩ := hl.passive_binary_components hf
  have hn : ¬ AC f := by rcases hf with rfl | rfl <;> simp [AC]
  obtain ⟨x, y, hshape, hx, hy⟩ := ((ht.reducesModulo hr).trans hw).symm.rigid_binary_shape hn
  exact ⟨x, y, hshape, ha.sound.trans hx.sound, hb.sound.trans hy.sound⟩

/-- A partial-decryption-valued projection reaches an actual pair selection. -/
theorem EqE.projection_partialDecrypt_inversion {f : Unary} (hf : f = .fst ∨ f = .snd)
    {a k c : Term V} (he : EqE (.unary f a) (.binary .partialDecrypt k c)) :
    ∃ x y, ReducesModulo a (.binary .pair x y) ∧
      EqE (if f = .fst then x else y) (.binary .partialDecrypt k c) := by
  obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp he
  rcases hl.projection_cases hf with ⟨_, _, ht⟩ | ⟨x, y, hp, hout⟩
  · obtain ⟨_, _, hc, _⟩ := hr.passive_binary_components (Or.inr rfl)
    cases (ht.symm.trans hc).head_eq
  · exact ⟨x, y, hp, hout.sound.trans hr.sound.symm⟩

/-- A decryption returning a partial-decryption value must reach E5 or E6. -/
theorem EqE.decryption_partialDecrypt_inversion {a b k c : Term V}
    (he : EqE (.binary .dec a b) (.binary .partialDecrypt k c)) :
    ∃ p, DecryptionMatch a b p ∧ EqE p (.binary .partialDecrypt k c) := by
  obtain ⟨t, hl, hr⟩ := (eqE_iff_join _ _).mp he
  rcases hl.decryption_cases with ⟨_, _, _, _, ht⟩ | ⟨p, hp, hout⟩
  · obtain ⟨_, _, hc, _⟩ := hr.passive_binary_components (Or.inr rfl)
    cases (ht.symm.trans hc).head_eq
  · exact ⟨p, hp, hout.sound.trans hr.sound.symm⟩

theorem tuple_not_eqE_partialDecrypt (xs : List (Term V)) (k c : Term V) :
    ¬ EqE (Term.tuple xs) (.binary .partialDecrypt k c) := by
  cases xs with
  | nil =>
    intro he
    obtain ⟨_, _, hshape, _⟩ := he.symm.passive_binary_irreducible_shape
      (Or.inr rfl) (constant_irreducible .bottom)
    cases hshape
  | cons a xs =>
    intro he
    have hf := ((EqE.passive_binary_iff .pair .partialDecrypt (Or.inl rfl) (Or.inr rfl) _ _ _ _).mp he).1
    cases hf

/-- Partial-decryption constructor arguments are not tuple selectors. All chains
over tuples with non-pair, non-partial-decryption fields miss such values. -/
theorem ProjectionChain.not_partialDecrypt_of_tuple {σ : V → Term W} {v : V} {r : Term V}
    (hc : ProjectionChain v r) (xs : List (Term W)) (hv : EqE (σ v) (Term.tuple xs))
    (hp : ∀ t ∈ xs, ∀ x y, ¬ EqE t (.binary .pair x y))
    (hd : ∀ t ∈ xs, ∀ k c, ¬ EqE t (.binary .partialDecrypt k c)) (k c : Term W) :
    ¬ EqE (r.subst σ) (.binary .partialDecrypt k c) := by
  intro he
  cases hc with
  | handle => exact tuple_not_eqE_partialDecrypt xs k c (hv.symm.trans he)
  | step f hf hc =>
    obtain ⟨x, y, hpair, _⟩ := he.projection_partialDecrypt_inversion hf
    obtain ⟨i, hi, rfl⟩ := hc.pair_origin xs hv hp hpair.sound
    rcases hf with rfl | rfl
    · have hs : EqE (((Term.var v : Term V).project i).subst σ) xs[i] := by
        rw [Term.subst_project]
        exact (EqE.unary .fst (hv.drop i)).trans (project_tuple_get xs i hi)
      exact hd xs[i] (List.getElem_mem hi) k c (hs.symm.trans he)
    · have hs : EqE ((Term.unary .snd ((Term.var v).drop i) : Term V).subst σ)
          (Term.tuple (xs.drop (i + 1))) := by
        rw [← Term.drop_succ_outer, Term.subst_drop]
        exact (hv.drop (i + 1)).trans (tuple_drop_reduces xs (i + 1) (by omega)).sound
      exact tuple_not_eqE_partialDecrypt _ k c (hs.symm.trans he)

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

theorem ballot_fields_not_partialDecrypt (ns : Names n) (i : Fin 2)
    (chosen : Fin (n + 1) → Ground) (t : Ground) (ht : t ∈ ballotFields ns i chosen) (k c : Ground) :
    ¬ EqE t (.binary .partialDecrypt k c) := by
  simp only [ballotFields, List.mem_append, List.mem_map, List.mem_singleton] at ht
  rcases ht with (⟨j, _, rfl⟩ | ⟨j, _, rfl⟩) | rfl
  · exact penc_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ _ _
  · exact spk_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ _ _ _
  · exact spk_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ _ _ _

theorem voter_projection_not_partialDecrypt (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (i : Fin 2) {r : Recipe 3}
    (hc : ProjectionChain i.succ r) (k c : Ground) :
    ¬ EqE ((frame ns swap left right).eval r) (.binary .partialDecrypt k c) := by
  have hv : EqE ((frame ns swap left right).value i.succ)
      (Term.tuple (ballotFields ns i (choice swap left right i).value)) := by
    rw [frame_voter_handle]
    exact .refl _
  exact hc.not_partialDecrypt_of_tuple _ hv (ballot_fields_not_pair ns i _)
    (ballot_fields_not_partialDecrypt ns i _) k c

/-- No chain on any initial handle returns a partial-decryption value. Final
frames publishing such values are deliberately outside this statement. -/
theorem frame_projection_not_partialDecrypt (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (v : Fin 3) {r : Recipe 3}
    (hc : ProjectionChain v r) (k c : Ground) :
    ¬ EqE ((frame ns swap left right).eval r) (.binary .partialDecrypt k c) := by
  intro he
  fin_cases v
  · cases hc with
    | handle => exact pk_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ he
    | step f hf hc =>
      obtain ⟨x, y, hp, _⟩ := he.projection_partialDecrypt_inversion hf
      exact hc.not_pair_of_handle (σ := (frame ns swap left right).value)
        (fun _ _ => pk_not_eqE_pair _ _ _) x y hp.sound
  · exact voter_projection_not_partialDecrypt ns swap left right 0 hc k c he
  · exact voter_projection_not_partialDecrypt ns swap left right 1 hc k c he

end ExplainableCrypto.Helios.Symbolic.Historical.General
