import ExplainableCrypto.Helios.Symbolic.StuckDestructorStructure

namespace ExplainableCrypto.Helios.Symbolic

/-- The two projection heads and the decryption head used by stuck-value origins. -/
def Term.StuckDestructorHead (t : Ground) : Prop :=
  (∃ f, (f = .fst ∨ f = .snd) ∧ t.headTag = .unary f) ∨ t.headTag = .binary .dec

namespace Frame
variable {policy : Finset Nat} {handles : Nat}

/-- Shared head classification with explicit frame-specific exclusions. -/
theorem minimum_normal_stuck_head_of_origins (φ : Frame policy handles) (restricted : Finset Nat)
    (hproject : ∀ f : Unary, f = .fst ∨ f = .snd → ∀ a : Recipe handles,
      MinimalRecipe restricted φ.value (.unary f a) → ∀ x y,
      EqE (φ.eval a) (.binary .pair x y) →
      (∃ x y, EqE (φ.eval (.unary f a)) (.binary .pair x y)) ∨
      (∃ k r m, EqE (φ.eval (.unary f a)) (.ternary .penc k r m)) ∨
      (∃ k r m c, EqE (φ.eval (.unary f a)) (.spk k r m c)))
    (hdec : ∀ a b : Recipe handles, MinimalRecipe restricted φ.value (.binary .dec a b) →
      ∀ out, ¬ DecryptionMatch (φ.eval a) (φ.eval b) out)
    (hhandles : ∀ t : Ground, Irreducible t → t.StuckDestructorHead → ∀ v, ¬ EqE (φ.value v) t)
    (r : Recipe handles) (hm : MinimalRecipe restricted φ.value r) {t : Ground}
    (ht : Irreducible t) (hk : t.StuckDestructorHead) (he : EqE (φ.eval r) t) :
    (r.subst (fun _ => (.const .bottom : Ground))).headTag = t.headTag := by
  have notPair {a b : Ground} (hv : EqE (φ.eval r) (.binary .pair a b)) : False := by
    obtain ⟨_, _, rfl, _⟩ := (hv.symm.trans he).passive_binary_irreducible_shape (Or.inl rfl) ht
    simp [Term.StuckDestructorHead, Term.headTag] at hk
  cases r with
  | name a => exact ((irreducible_eqE_iff_base (name_irreducible a) ht).mp he).head_eq
  | const c => exact ((irreducible_eqE_iff_base (constant_irreducible c) ht).mp he).head_eq
  | var v => exact False.elim (hhandles t ht hk v he)
  | unary f a =>
    have projection (hf : f = .fst ∨ f = .snd) : ((Term.unary f a).subst (fun _ => (.const .bottom : Ground))).headTag = t.headTag := by
      obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp he
      rcases hl.projection_cases hf with ⟨_, _, hw⟩ | ⟨x, y, hp, _⟩
      · exact ((ht.reducesModulo hr).trans hw).head_eq.symm
      · rcases hproject f hf a hm x y hp.sound with ⟨_, _, hv⟩ | ⟨_, _, _, hv⟩ | ⟨_, _, _, _, hv⟩
        · exact False.elim (notPair hv)
        · obtain ⟨_, _, _, rfl, _⟩ := (hv.symm.trans he).penc_irreducible_shape ht
          simp [Term.StuckDestructorHead, Term.headTag] at hk
        · obtain ⟨_, _, _, _, rfl, _⟩ := (hv.symm.trans he).spk_irreducible_shape ht
          simp [Term.StuckDestructorHead, Term.headTag] at hk
    cases f with
    | pk =>
      obtain ⟨_, rfl, _⟩ := he.pk_irreducible_shape ht
      rfl
    | fst => exact projection (Or.inl rfl)
    | snd => exact projection (Or.inr rfl)
  | binary f a b =>
    cases f with
    | pair =>
      obtain ⟨_, _, rfl, _⟩ := he.passive_binary_irreducible_shape (Or.inl rfl) ht
      rfl
    | partialDecrypt =>
      obtain ⟨_, _, rfl, _⟩ := he.passive_binary_irreducible_shape (Or.inr rfl) ht
      rfl
    | mul =>
      rcases he.mul_irreducible_shape ht with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
        simp [Term.StuckDestructorHead, Term.headTag] at hk
    | add =>
      rcases he.add_irreducible_shape ht with ⟨_, _, rfl⟩ | rfl | rfl <;>
        simp [Term.StuckDestructorHead, Term.headTag] at hk
    | compose =>
      obtain ⟨_, _, rfl⟩ := he.compose_irreducible_shape ht
      simp [Term.StuckDestructorHead, Term.headTag] at hk
    | dec =>
      obtain ⟨_, _, rfl, _⟩ := decryption_normal_shape_of_no_match _ _
        (hdec a b hm) ht he
      rfl
  | ternary f a b c =>
    cases f with
    | penc =>
      obtain ⟨_, _, _, rfl, _⟩ := he.penc_irreducible_shape ht
      rfl
    | checkspk =>
      obtain ⟨_, _, _, rfl, _⟩ := hm.proof_check_normal_shape a b c ht he
      rfl
  | spk a b c d =>
    obtain ⟨_, _, _, _, rfl, _⟩ := he.spk_irreducible_shape ht
    rfl

/-- A minimum stuck projection retains its selector and a non-pair argument. -/
theorem minimum_stuck_projection_form_of_head (φ : Frame policy handles) (restricted : Finset Nat)
    (hproject : ∀ f : Unary, f = .fst ∨ f = .snd → ∀ a : Recipe handles,
      MinimalRecipe restricted φ.value (.unary f a) → ∀ x y,
      EqE (φ.eval a) (.binary .pair x y) →
      (∃ x y, EqE (φ.eval (.unary f a)) (.binary .pair x y)) ∨
      (∃ k r m, EqE (φ.eval (.unary f a)) (.ternary .penc k r m)) ∨
      (∃ k r m c, EqE (φ.eval (.unary f a)) (.spk k r m c)))
    (hhead : ∀ r : Recipe handles, MinimalRecipe restricted φ.value r →
      ∀ t : Ground, Irreducible t → t.StuckDestructorHead → EqE (φ.eval r) t →
        (r.subst (fun _ => (.const .bottom : Ground))).headTag = t.headTag)
    (r : Recipe handles) (hm : MinimalRecipe restricted φ.value r)
    (f : Unary) (hf : f = .fst ∨ f = .snd) {a : Ground}
    (hn : ∀ x y, ¬ EqE a (.binary .pair x y))
    (he : EqE (φ.eval r) (.unary f a)) :
    ∃ b, r = .unary f b ∧ ∀ x y, ¬ EqE (φ.eval b) (.binary .pair x y) := by
  obtain ⟨t, hpath, ht⟩ := exists_normal_form (.unary f a)
  have he' := hpath.to_modulo.sound
  obtain ⟨a', rfl, _⟩ := projection_normal_shape_of_no_pair f hf a hn ht he'
  have hh := hhead r hm _ ht
    (Or.inl ⟨f, hf, rfl⟩) (he.trans he')
  have hsyntax : ∃ b, r = .unary f b := by
    cases r with
    | unary g b =>
      have hgf : g = f := by simpa [Term.subst, Term.headTag] using hh
      subst g
      exact ⟨b, rfl⟩
    | const c => cases c <;> cases hh
    | binary g b c => cases g <;> cases hh
    | name _ | var _ | ternary _ _ _ _ | spk _ _ _ _ => cases hh
  obtain ⟨b, rfl⟩ := hsyntax
  refine ⟨b, rfl, ?_⟩
  intro x y hp
  rcases hproject f hf b hm x y hp with ⟨_, _, hv⟩ | ⟨_, _, _, hv⟩ | ⟨_, _, _, _, hv⟩
  · obtain ⟨u, v, hp, _⟩ := (he.symm.trans hv).projection_pair_inversion hf
    exact hn u v hp.sound
  · obtain ⟨u, v, hp, _⟩ := (he.symm.trans hv).projection_penc_inversion hf
    exact hn u v hp.sound
  · obtain ⟨u, v, hp, _⟩ := (he.symm.trans hv).projection_spk_inversion hf
    exact hn u v hp.sound

/-- A minimum stuck decryption retains both ordered arguments. -/
theorem minimum_stuck_decryption_form_of_head (φ : Frame policy handles) (restricted : Finset Nat)
    (hdec : ∀ a b : Recipe handles, MinimalRecipe restricted φ.value (.binary .dec a b) →
      ∀ out, ¬ DecryptionMatch (φ.eval a) (φ.eval b) out)
    (hhead : ∀ r : Recipe handles, MinimalRecipe restricted φ.value r →
      ∀ t : Ground, Irreducible t → t.StuckDestructorHead → EqE (φ.eval r) t →
        (r.subst (fun _ => (.const .bottom : Ground))).headTag = t.headTag)
    (r : Recipe handles) (hm : MinimalRecipe restricted φ.value r) {a b : Ground}
    (hn : ∀ out, ¬ DecryptionMatch a b out) (he : EqE (φ.eval r) (.binary .dec a b)) :
    ∃ u v, r = .binary .dec u v ∧ ∀ out, ¬ DecryptionMatch (φ.eval u) (φ.eval v) out := by
  obtain ⟨t, hpath, ht⟩ := exists_normal_form (.binary .dec a b)
  have he' := hpath.to_modulo.sound
  obtain ⟨_, _, rfl, _⟩ := decryption_normal_shape_of_no_match a b hn ht he'
  have hh := hhead r hm _ ht
    (Or.inr rfl) (he.trans he')
  have hsyntax : ∃ u v, r = .binary .dec u v := by
    cases r with
    | binary g u v =>
      cases g <;> try cases hh
      exact ⟨u, v, rfl⟩
    | const c => cases c <;> cases hh
    | name _ | var _ | unary _ _ | ternary _ _ _ _ | spk _ _ _ _ => cases hh
  obtain ⟨u, v, rfl⟩ := hsyntax
  exact ⟨u, v, rfl, hdec u v hm⟩

end Frame
end ExplainableCrypto.Helios.Symbolic
