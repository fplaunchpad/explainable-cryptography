import ExplainableCrypto.Helios.Symbolic.DecryptionPaths
import ExplainableCrypto.Helios.Symbolic.MinimalRecipes

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type} {restricted : Finset Nat} {σ : V → Term W}

/-- The termination measure never exceeds raw syntax size. -/
theorem Term.cryptoWeight_le_nodeCount (t : Term V) : t.cryptoWeight ≤ t.nodeCount := by
  induction t with
  | binary f a b ha hb => cases f <;> simp_all [Term.cryptoWeight, Term.nodeCount] <;> omega
  | _ => simp_all [Term.cryptoWeight, Term.nodeCount] <;> omega

/-- A sufficient minimum criterion for identity substitution, used to retain
nontrivial controls. It is not a necessary criterion for minimality. -/
theorem MinimalRecipe.of_irreducible_weight {r : Term V} (hp : r.Public restricted)
    (hi : Irreducible r) (hw : r.cryptoWeight = r.nodeCount) :
    MinimalRecipe restricted Term.var r := by
  refine ⟨hp, ?_⟩
  intro s _ he
  simp only [Term.subst_var] at he
  obtain ⟨t, hr, hs⟩ := (eqE_iff_join _ _).mp he
  have hweight := (hi.reducesModulo hr).weight_eq
  have hle := hs.weight_le
  have hsize := s.cryptoWeight_le_nodeCount
  omega

/-- Any E5/E6 match would replace the whole recipe by its explicit public plaintext. -/
theorem MinimalRecipe.no_explicit_decryption_match (a key nonce p : Term V)
    (h : MinimalRecipe restricted σ (.binary .dec a (.ternary .penc key nonce p)))
    (m : Term W) :
    ¬ DecryptionMatch (a.subst σ) ((.ternary .penc key nonce p : Term V).subst σ) m := by
  intro hm
  have he : EqE ((.binary .dec a (.ternary .penc key nonce p) : Term V).subst σ) (p.subst σ) :=
    hm.reduces.sound.trans hm.explicit_plaintext.symm
  apply h.no_smaller h.isPublic.2.2.2 he
  simp only [Term.nodeCount]
  omega

/-- Every actual path from this minimum recipe retains the decryption constructor. -/
theorem MinimalRecipe.explicit_decryption_path (a key nonce p : Term V)
    (h : MinimalRecipe restricted σ (.binary .dec a (.ternary .penc key nonce p)))
    {t : Term W}
    (ht : ReducesModulo ((.binary .dec a (.ternary .penc key nonce p) : Term V).subst σ) t) :
    ∃ a' b', ReducesModulo (a.subst σ) a' ∧
      ReducesModulo ((.ternary .penc key nonce p : Term V).subst σ) b' ∧
      BaseEq t (.binary .dec a' b') := by
  rcases ht.decryption_cases with hs | ⟨m, hm, _⟩
  · exact hs
  · exact False.elim (h.no_explicit_decryption_match a key nonce p m hm)

/-- An irreducible representative of a minimum explicit-ciphertext decrypt
retains its head and both evaluated argument values. -/
theorem MinimalRecipe.explicit_decryption_normal_shape (a key nonce p : Term V)
    (h : MinimalRecipe restricted σ (.binary .dec a (.ternary .penc key nonce p)))
    {t : Term W} (ht : Irreducible t)
    (he : EqE ((.binary .dec a (.ternary .penc key nonce p) : Term V).subst σ) t) :
    ∃ a' b', t = .binary .dec a' b' ∧ EqE (a.subst σ) a' ∧
      EqE ((.ternary .penc key nonce p : Term V).subst σ) b' := by
  obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp he
  obtain ⟨a₁, b₁, ha, hb, hw⟩ := h.explicit_decryption_path a key nonce p hl
  obtain ⟨a₂, b₂, ht₂, ha₂, hb₂⟩ :=
    ((ht.reducesModulo hr).trans hw).symm.rigid_binary_shape (by simp [AC])
  exact ⟨a₂, b₂, ht₂, ha.sound.trans ha₂.sound, hb.sound.trans hb₂.sound⟩

/-- No ciphertext-valued result is possible in this minimum-recipe case,
including ciphertext targets with reducible components. -/
theorem MinimalRecipe.explicit_decryption_not_ciphertext (a key nonce p : Term V)
    (h : MinimalRecipe restricted σ (.binary .dec a (.ternary .penc key nonce p)))
    (k r m : Term W) :
    ¬ EqE ((.binary .dec a (.ternary .penc key nonce p) : Term V).subst σ)
      (.ternary .penc k r m) := by
  intro he
  obtain ⟨out, hm, _⟩ := he.decryption_penc_inversion
  exact h.no_explicit_decryption_match a key nonce p out hm

/-- Any recipe for a constant-plaintext ciphertext has the same smaller public
plaintext available, even if its own syntax is a handle, projection or product. -/
theorem MinimalRecipe.constant_plaintext_no_decryption_match (a b : Term V)
    (h : MinimalRecipe restricted σ (.binary .dec a b)) (key nonce : Term W) (c : Constant)
    (hb : EqE (b.subst σ) (.ternary .penc key nonce (.const c))) (m : Term W) :
    ¬ DecryptionMatch (a.subst σ) (b.subst σ) m := by
  intro hm
  have hmPath := hm.reduces
  obtain ⟨k, r, _, hc⟩ := hm
  have hp : EqE (.const c : Term W) m :=
    ((EqE.penc_iff _ _ _ _ _ _).mp (hb.symm.trans hc.sound)).2.2
  have he : EqE ((.binary .dec a b : Term V).subst σ) ((.const c : Term V).subst σ) :=
    hmPath.sound.trans hp.symm
  apply h.no_smaller (s := .const c) trivial he
  have := a.nodeCount_pos
  simp only [Term.nodeCount]
  omega

theorem MinimalRecipe.constant_plaintext_decryption_normal_shape (a b : Term V)
    (h : MinimalRecipe restricted σ (.binary .dec a b)) (key nonce : Term W) (c : Constant)
    (hb : EqE (b.subst σ) (.ternary .penc key nonce (.const c)))
    {t : Term W} (ht : Irreducible t) (he : EqE ((.binary .dec a b : Term V).subst σ) t) :
    ∃ a' b', t = .binary .dec a' b' ∧ EqE (a.subst σ) a' ∧ EqE (b.subst σ) b' :=
  decryption_normal_shape_of_no_match _ _
    (h.constant_plaintext_no_decryption_match a b key nonce c hb) ht he

/-- The source's normal-form composition clause for an explicit-ciphertext argument. -/
theorem MinimalRecipe.explicit_decryption_normal_form (a key nonce p : Term V)
    (h : MinimalRecipe restricted σ (.binary .dec a (.ternary .penc key nonce p)))
    {a' b' t : Term W} (ha : Irreducible a') (hb : Irreducible b') (ht : Irreducible t)
    (hea : EqE (a.subst σ) a')
    (heb : EqE ((.ternary .penc key nonce p : Term V).subst σ) b')
    (he : EqE ((.binary .dec a (.ternary .penc key nonce p) : Term V).subst σ) t) :
    BaseEq t (.binary .dec a' b') :=
  decryption_normal_form_of_no_match _ _
    (h.no_explicit_decryption_match a key nonce p) ha hb ht hea heb he

end ExplainableCrypto.Helios.Symbolic
