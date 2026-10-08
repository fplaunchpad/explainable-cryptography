import ExplainableCrypto.Helios.Symbolic.TrusteeFreeSyntax

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type} {secret : Nat}

theorem BaseEquation.trustee_free {a b : Term V} (h : BaseEquation a b) :
    a.TrusteeFree secret ↔ b.TrusteeFree secret := by
  cases h with
  | zero_one | zero_zero => simp [Term.TrusteeFree]
  | comm f hf => cases f <;> simp_all [AC, Term.TrusteeFree, and_comm]
  | assoc f hf => cases f <;> simp_all [AC, Term.TrusteeFree, and_assoc]

theorem BaseEq.trustee_free {a b : Term V} (h : BaseEq a b) :
    a.TrusteeFree secret ↔ b.TrusteeFree secret := by
  induction h with
  | equation h => exact h.trustee_free
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | unary f h ih => exact ih
  | binary f ha hb ia ib =>
    have hk : EqE _ (.name secret) ↔ EqE _ (.name secret) :=
      ⟨fun h => ha.sound.symm.trans h, fun h => ha.sound.trans h⟩
    simp only [Term.TrusteeFree, ia, ib, hk]
  | ternary f ha hb hc ia ib ic => simp only [Term.TrusteeFree, ia, ib, ic]
  | spk ha hb hc hd ia ib ic id => simp only [Term.TrusteeFree, ia, ib, ic, id]

theorem RootStep.trustee_free {a b : Term V} (h : RootStep a b)
    (ha : a.TrusteeFree secret) : b.TrusteeFree secret := by
  cases h <;> simp_all [Term.TrusteeFree]

theorem Context.trustee_free (c : Context V) {a b : Term V} (he : EqE a b)
    (h : a.TrusteeFree secret → b.TrusteeFree secret) :
    (c.fill a).TrusteeFree secret → (c.fill b).TrusteeFree secret := by
  induction c with
  | hole => exact h
  | binaryLeft f c t ih =>
    rintro ⟨hc, ht, hg⟩
    exact ⟨ih hc, ht, fun hf hk => hg hf ((c.congr he).trans hk)⟩
  | _ => simp_all [Context.fill, Term.TrusteeFree]

theorem RewriteStep.trustee_free {a b : Term V} (h : RewriteStep a b)
    (ha : a.TrusteeFree secret) : b.TrusteeFree secret := by
  obtain ⟨c, l, r, hr, rfl, rfl⟩ := h
  exact c.trustee_free hr.sound hr.trustee_free ha

theorem ModuloStep.trustee_free {a b : Term V} (h : ModuloStep a b)
    (ha : a.TrusteeFree secret) : b.TrusteeFree secret := by
  obtain ⟨x, y, hx, hxy, hy⟩ := h
  exact hy.trustee_free.mp (hxy.trustee_free (hx.trustee_free.mp ha))

theorem ReducesModulo.trustee_free {a b : Term V} (h : ReducesModulo a b)
    (ha : a.TrusteeFree secret) : b.TrusteeFree secret := by
  induction h with
  | base h => exact h.trustee_free.mp ha
  | head hs _ ih => exact ih (hs.trustee_free ha)

theorem TrusteeFreeValue.of_eq {a b : Term V} (ha : TrusteeFreeValue secret a)
    (he : EqE a b) : TrusteeFreeValue secret b := by
  obtain ⟨u, hu, hf⟩ := ha
  exact ⟨u, he.symm.trans hu, hf⟩

theorem TrusteeFreeValue.irreducible {t : Term V} (h : TrusteeFreeValue secret t)
    (ht : Irreducible t) : t.TrusteeFree secret := by
  obtain ⟨u, hu, hf⟩ := h
  obtain ⟨w, htw, huw⟩ := (eqE_iff_join _ _).mp hu
  exact (ht.reducesModulo htw).trustee_free.mpr (huw.trustee_free hf)

theorem TrusteeFreeValue.normal_rep {t : Term V} (h : TrusteeFreeValue secret t) :
    ∃ u, EqE t u ∧ Irreducible u ∧ u.TrusteeFree secret := by
  obtain ⟨u, hp, hi⟩ := exists_normal_form t
  exact ⟨u, hp.sound, hi, (h.of_eq hp.sound).irreducible hi⟩

/-- No E expansion or erasing detour makes an actual secret-keyed partial free. -/
theorem trustee_partial_not_free (binding : Term V) :
    ¬ TrusteeFreeValue secret (.binary .partialDecrypt (.name secret) binding) := by
  intro h
  obtain ⟨u, he, hi, hf⟩ := h.normal_rep
  obtain ⟨k, c, rfl, hk, _⟩ := he.passive_binary_irreducible_shape (Or.inr rfl) hi
  exact hf.2.2 rfl hk.symm

end ExplainableCrypto.Helios.Symbolic
