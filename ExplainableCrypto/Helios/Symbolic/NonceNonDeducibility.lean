import ExplainableCrypto.Helios.Symbolic.NonceProtection
import ExplainableCrypto.Helios.Symbolic.GlobalConfluence
import ExplainableCrypto.Helios.Symbolic.Frames

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type} {restricted : Finset Nat}

theorem BaseEquation.nonce_safe {a b : Term V} (h : BaseEquation a b) :
    a.nonceSafe restricted = b.nonceSafe restricted := by
  cases h <;> simp [Term.nonceSafe, Bool.and_comm, Bool.and_assoc]

theorem BaseEq.nonce_safe {a b : Term V} (h : BaseEq a b) :
    a.nonceSafe restricted = b.nonceSafe restricted := by
  induction h with
  | equation h => exact h.nonce_safe
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | unary f _ ih => cases f <;> simp_all [Term.nonceSafe]
  | binary f _ _ ih₁ ih₂ => simp_all [Term.nonceSafe]
  | ternary f _ _ _ ih₁ ih₂ ih₃ => cases f <;> simp_all [Term.nonceSafe]
  | spk => rfl

theorem RootStep.nonce_safe {a b : Term V} (h : RootStep a b)
    (ha : a.nonceSafe restricted = true) : b.nonceSafe restricted = true := by
  cases h <;> simp_all [Term.nonceSafe]

private theorem context_safe (c : Context V) {a b : Term V}
    (h : a.nonceSafe restricted = true → b.nonceSafe restricted = true) :
    (c.fill a).nonceSafe restricted = true → (c.fill b).nonceSafe restricted = true := by
  induction c with
  | hole => exact h
  | unary f c ih => cases f <;> simp_all [Context.fill, Term.nonceSafe]
  | binaryLeft f c t ih => simp_all [Context.fill, Term.nonceSafe]
  | binaryRight f t c ih => simp_all [Context.fill, Term.nonceSafe]
  | ternaryFirst f c t u ih => cases f <;> simp_all [Context.fill, Term.nonceSafe]
  | ternarySecond f t c u ih => cases f <;> simp_all [Context.fill, Term.nonceSafe]
  | ternaryThird f t u c ih => cases f <;> simp_all [Context.fill, Term.nonceSafe]
  | spkFirst | spkSecond | spkThird | spkFourth => simp [Context.fill, Term.nonceSafe]

theorem RewriteStep.nonce_safe {a b : Term V} (h : RewriteStep a b)
    (ha : a.nonceSafe restricted = true) : b.nonceSafe restricted = true := by
  obtain ⟨c, l, r, hr, rfl, rfl⟩ := h
  exact context_safe c hr.nonce_safe ha

theorem ModuloStep.nonce_safe {a b : Term V} (h : ModuloStep a b)
    (ha : a.nonceSafe restricted = true) : b.nonceSafe restricted = true := by
  obtain ⟨x, y, hx, hxy, hy⟩ := h
  rw [← hy.nonce_safe]
  exact hxy.nonce_safe (hx.nonce_safe ▸ ha)

theorem ReducesModulo.nonce_safe {a b : Term V} (h : ReducesModulo a b)
    (ha : a.nonceSafe restricted = true) : b.nonceSafe restricted = true := by
  induction h with
  | base h => exact h.nonce_safe ▸ ha
  | head hs _ ih => exact ih (hs.nonce_safe ha)

theorem Term.Public.nonce_safe (t : Term V) (h : t.Public restricted) :
    t.nonceSafe restricted = true := by
  induction t with
  | unary f a ih => cases f <;> simp_all [Term.Public, Term.nonceSafe]
  | ternary f a b c ia ib ic => cases f <;> simp_all [Term.Public, Term.nonceSafe]
  | _ => simp_all [Term.Public, Term.nonceSafe]

theorem Term.nonce_safe_subst (t : Term V) (σ : V → Term W)
    (ht : t.nonceSafe restricted = true) (hσ : ∀ v, (σ v).nonceSafe restricted = true) :
    (t.subst σ).nonceSafe restricted = true := by
  induction t with
  | unary f a ih => cases f <;> simp_all [Term.subst, Term.nonceSafe]
  | ternary f a b c ia ib ic => cases f <;> simp_all [Term.subst, Term.nonceSafe]
  | _ => simp_all [Term.subst, Term.nonceSafe]

/-- Forward protection plus confluence excludes equality to an irreducible
protected name; protection is not assumed invariant under arbitrary E expansion. -/
theorem nonce_safe_not_eqE_name {t : Term V} (ht : t.nonceSafe restricted = true)
    {n : Nat} (hn : n ∈ restricted) : ¬ EqE t (.name n) := by
  intro h
  obtain ⟨w, hw, hnw⟩ := (eqE_iff_join _ _).mp h
  have hs := hw.nonce_safe ht
  have he := (name_irreducible n).reducesModulo hnw
  rw [← he.nonce_safe] at hs
  simp [Term.nonceSafe, hn] at hs

/-- Every public recipe over a protected frame fails to deduce a restricted name.
The per-handle invariant is a substantive premise, not automatic for all frames. -/
theorem Frame.nonce_not_deducible {handles : Nat} (φ : Frame restricted handles)
    (hφ : ∀ i, (φ.value i).nonceSafe restricted = true)
    (r : Recipe handles) (hr : r.Public restricted) {n : Nat} (hn : n ∈ restricted) :
    ¬ EqE (φ.eval r) (.name n) :=
  nonce_safe_not_eqE_name (r.nonce_safe_subst φ.value (hr.nonce_safe r) hφ) hn

end ExplainableCrypto.Helios.Symbolic
