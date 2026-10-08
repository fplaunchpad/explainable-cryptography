import ExplainableCrypto.Helios.Symbolic.DecryptionOverlap

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Every active decryption root is E5 or E6, with all repeated fields exposed
through E0 equalities. No constructor-separation claim for full E is assumed. -/
theorem RootModuloStep.decryption_cases {a b t : Term V}
    (h : RootModuloStep (.binary .dec a b) t) :
    (∃ k r m, BaseEq a k ∧ BaseEq b (keyCiphertext k r m) ∧ BaseEq m t) ∨
    (∃ k r m, BaseEq a (.binary .partialDecrypt k (keyCiphertext k r m)) ∧
      BaseEq b (keyCiphertext k r m) ∧ BaseEq m t) := by
  obtain ⟨l, r, he, hr, ht⟩ := h
  cases hr with
  | decrypt =>
    obtain ⟨_, ha, hb⟩ := (BaseEq.binary_iff .dec .dec (by simp [AC]) (by simp [AC]) _ _ _ _).mp he
    exact Or.inl ⟨_, _, _, ha, hb, ht⟩
  | partial_decrypt =>
    obtain ⟨_, ha, hb⟩ := (BaseEq.binary_iff .dec .dec (by simp [AC]) (by simp [AC]) _ _ _ _).mp he
    exact Or.inr ⟨_, _, _, ha, hb, ht⟩
  | _ => have hh := he.head_eq; cases hh

/-- All root decryption rules versus an arbitrary step in their left argument. -/
theorem decryption_root_left_joined {a b t a' : Term V}
    (hroot : RootModuloStep (.binary .dec a b) t) (hinner : ModuloStep a a') :
    JoinModulo t (.binary .dec a' b) := by
  rcases hroot.decryption_cases with ⟨k, r, m, ha, hb, hm⟩ | ⟨k, r, m, ha, hb, hm⟩
  · exact (decrypt_key_step_joined k r m (hinner.pre_base ha.symm)).of_base
      hm.symm (.binary .dec (.refl _) hb)
  · exact (partial_decrypt_left_step_joined k r m (hinner.pre_base ha.symm)).of_base
      hm.symm (.binary .dec (.refl _) hb)

/-- All root decryption rules versus an arbitrary step in their right argument. -/
theorem decryption_root_right_joined {a b t b' : Term V}
    (hroot : RootModuloStep (.binary .dec a b) t) (hinner : ModuloStep b b') :
    JoinModulo t (.binary .dec a b') := by
  rcases hroot.decryption_cases with ⟨k, r, m, ha, hb, hm⟩ | ⟨k, r, m, ha, hb, hm⟩
  · exact (decrypt_ciphertext_step_joined k r m (hinner.pre_base hb.symm)).of_base
      hm.symm (.binary .dec ha (.refl _))
  · exact (partial_decrypt_right_step_joined k r m (hinner.pre_base hb.symm)).of_base
      hm.symm (.binary .dec ha (.refl _))

/-- A reusable non-AC constructor argument. Root/internal joins are explicit
premises, separately discharged for active decryption below. -/
theorem locally_confluent_at_rigid_binary (f : Binary) (hf : ¬ AC f) (a b : Term V)
    (ha : LocallyConfluentAt a) (hb : LocallyConfluentAt b)
    (hl : ∀ t a', RootModuloStep (.binary f a b) t → ModuloStep a a' →
      JoinModulo t (.binary f a' b))
    (hr : ∀ t b', RootModuloStep (.binary f a b) t → ModuloStep b b' →
      JoinModulo t (.binary f a b')) : LocallyConfluentAt (.binary f a b) := by
  intro u v hu hv
  rcases hu.rigid_binary_cases hf with hu | ⟨a', hu, heu⟩ | ⟨b', hu, heu⟩
  · rcases hv.rigid_binary_cases hf with hv | ⟨a', hv, hev⟩ | ⟨b', hv, hev⟩
    · exact ⟨v, .base (hu.outputs_base hv), .refl _⟩
    · exact (hl _ _ hu hv).of_base (.refl _) hev
    · exact (hr _ _ hu hv).of_base (.refl _) hev
  · rcases hv.rigid_binary_cases hf with hv | ⟨a'', hv, hev⟩ | ⟨b', hv, hev⟩
    · exact ((hl _ _ hv hu).of_base (.refl _) heu).symm
    · exact (JoinModulo.binary f (ha _ _ hu hv) (.refl b)).of_base heu hev
    · exact (JoinModulo.binary f ⟨a', .refl _, .single hu⟩
        ⟨b', .single hv, .refl _⟩).of_base heu hev
  · rcases hv.rigid_binary_cases hf with hv | ⟨a', hv, hev⟩ | ⟨b'', hv, hev⟩
    · exact ((hr _ _ hv hu).of_base (.refl _) heu).symm
    · exact (JoinModulo.binary f ⟨a', .single hv, .refl _⟩
        ⟨b', .refl _, .single hu⟩).of_base heu hev
    · exact (JoinModulo.binary f (.refl a) (hb _ _ hu hv)).of_base heu hev

/-- E5/E6 root/internal obligations are discharged. Only the two argument
local-confluence hypotheses remain, including for nonmatching decryption sources. -/
theorem locally_confluent_at_decryption (a b : Term V)
    (ha : LocallyConfluentAt a) (hb : LocallyConfluentAt b) :
    LocallyConfluentAt (.binary .dec a b) :=
  locally_confluent_at_rigid_binary .dec (by simp [AC]) a b ha hb
    (fun _ _ hroot hinner => decryption_root_left_joined hroot hinner)
    (fun _ _ hroot hinner => decryption_root_right_joined hroot hinner)

end ExplainableCrypto.Helios.Symbolic
