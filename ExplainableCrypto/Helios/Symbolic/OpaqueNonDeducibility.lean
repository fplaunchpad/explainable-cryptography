import ExplainableCrypto.Helios.Symbolic.OpaqueProtection
import ExplainableCrypto.Helios.Symbolic.NonceNonDeducibility
import ExplainableCrypto.Helios.Symbolic.GlobalConfluence
import ExplainableCrypto.Helios.Symbolic.Frames

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type} {restricted : Finset Nat}

theorem BaseEquation.opaque_safe {a b : Term V} (h : BaseEquation a b) :
    a.opaqueSafe restricted = b.opaqueSafe restricted := by
  cases h with
  | zero_one | zero_zero => rfl
  | comm f => cases f <;> simp [Term.opaqueSafe, Bool.and_comm]
  | assoc f => cases f <;> simp [Term.opaqueSafe, Bool.and_assoc]

theorem BaseEq.opaque_safe {a b : Term V} (h : BaseEq a b) :
    a.opaqueSafe restricted = b.opaqueSafe restricted := by
  induction h with
  | equation h => exact h.opaque_safe
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | unary f _ ih => cases f <;> simp_all [Term.opaqueSafe]
  | binary f _ _ ih₁ ih₂ => cases f <;> simp_all [Term.opaqueSafe]
  | ternary f _ _ _ ih₁ ih₂ ih₃ => cases f <;> simp_all [Term.opaqueSafe]
  | spk => rfl

theorem RootStep.opaque_safe {a b : Term V} (h : RootStep a b)
    (ha : a.opaqueSafe restricted = true) : b.opaqueSafe restricted = true := by
  cases h <;> simp_all [Term.opaqueSafe]

private theorem context_safe (c : Context V) {a b : Term V}
    (h : a.opaqueSafe restricted = true → b.opaqueSafe restricted = true) :
    (c.fill a).opaqueSafe restricted = true → (c.fill b).opaqueSafe restricted = true := by
  induction c with
  | hole => exact h
  | unary f c ih => cases f <;> simp_all [Context.fill, Term.opaqueSafe]
  | binaryLeft f c t ih => cases f <;> simp_all [Context.fill, Term.opaqueSafe]
  | binaryRight f t c ih => cases f <;> simp_all [Context.fill, Term.opaqueSafe]
  | ternaryFirst f c t u ih => cases f <;> simp_all [Context.fill, Term.opaqueSafe]
  | ternarySecond f t c u ih => cases f <;> simp_all [Context.fill, Term.opaqueSafe]
  | ternaryThird f t u c ih => cases f <;> simp_all [Context.fill, Term.opaqueSafe]
  | spkFirst | spkSecond | spkThird | spkFourth => simp [Context.fill, Term.opaqueSafe]

theorem RewriteStep.opaque_safe {a b : Term V} (h : RewriteStep a b)
    (ha : a.opaqueSafe restricted = true) : b.opaqueSafe restricted = true := by
  obtain ⟨c, l, r, hr, rfl, rfl⟩ := h
  exact context_safe c hr.opaque_safe ha

theorem ModuloStep.opaque_safe {a b : Term V} (h : ModuloStep a b)
    (ha : a.opaqueSafe restricted = true) : b.opaqueSafe restricted = true := by
  obtain ⟨x, y, hx, hxy, hy⟩ := h
  rw [← hy.opaque_safe]
  exact hxy.opaque_safe (hx.opaque_safe ▸ ha)

theorem ReducesModulo.opaque_safe {a b : Term V} (h : ReducesModulo a b)
    (ha : a.opaqueSafe restricted = true) : b.opaqueSafe restricted = true := by
  induction h with
  | base h => exact h.opaque_safe ▸ ha
  | head hs _ ih => exact ih (hs.opaque_safe ha)

theorem Term.Public.opaque_safe (t : Term V) (h : t.Public restricted) :
    t.opaqueSafe restricted = true := by
  induction t with
  | unary f a ih => cases f <;> simp_all [Term.Public, Term.opaqueSafe]
  | binary f a b ia ib => cases f <;> simp_all [Term.Public, Term.opaqueSafe]
  | ternary f a b c ia ib ic => cases f <;> simp_all [Term.Public, Term.opaqueSafe]
  | _ => simp_all [Term.Public, Term.opaqueSafe]

theorem Term.opaque_safe_subst (t : Term V) (σ : V → Term W)
    (ht : t.opaqueSafe restricted = true) (hσ : ∀ v, (σ v).opaqueSafe restricted = true) :
    (t.subst σ).opaqueSafe restricted = true := by
  induction t with
  | unary f a ih => cases f <;> simp_all [Term.subst, Term.opaqueSafe]
  | binary f a b ia ib => cases f <;> simp_all [Term.subst, Term.opaqueSafe]
  | ternary f a b c ia ib ic => cases f <;> simp_all [Term.subst, Term.opaqueSafe]
  | _ => simp_all [Term.subst, Term.opaqueSafe]

/-- Forward protection plus confluence excludes equality to an irreducible
protected name; protection is not assumed invariant under arbitrary E expansion. -/
theorem opaque_safe_not_eqE_name {t : Term V} (ht : t.opaqueSafe restricted = true)
    {n : Nat} (hn : n ∈ restricted) : ¬ EqE t (.name n) := by
  intro h
  obtain ⟨w, hw, hnw⟩ := (eqE_iff_join _ _).mp h
  have hs := hw.opaque_safe ht
  have he := (name_irreducible n).reducesModulo hnw
  rw [← he.opaque_safe] at hs
  simp [Term.opaqueSafe, hn] at hs

/-- Every public recipe over an opaque-protected frame fails to deduce a restricted name.
The per-handle invariant is a substantive premise, not automatic for all frames. -/
theorem Frame.opaque_safe_name_not_deducible {handles : Nat} (φ : Frame restricted handles)
    (hφ : ∀ i, (φ.value i).opaqueSafe restricted = true)
    (r : Recipe handles) (hr : r.Public restricted) {n : Nat} (hn : n ∈ restricted) :
    ¬ EqE (φ.eval r) (.name n) :=
  opaque_safe_not_eqE_name (r.opaque_safe_subst φ.value (hr.opaque_safe r) hφ) hn

/-- Reuse the old invariant wherever its stricter partial-field checks hold. -/
theorem Term.nonce_safe_opaque_safe (t : Term V) (ht : t.nonceSafe restricted = true) :
    t.opaqueSafe restricted = true := by
  induction t with
  | unary f a ih => cases f <;> simp_all [Term.nonceSafe,Term.opaqueSafe]
  | binary f a b ia ib => cases f <;> simp_all [Term.nonceSafe,Term.opaqueSafe]
  | ternary f a b c ia ib ic => cases f <;> simp_all [Term.nonceSafe,Term.opaqueSafe]
  | _ => simp_all [Term.nonceSafe,Term.opaqueSafe]

theorem OpaqueProtectedValue.of_safe {t : Term V} (h : t.opaqueSafe restricted = true) :
    OpaqueProtectedValue restricted t := ⟨t,.refl _,h⟩

/-- The representative property, unlike raw protection, is invariant under E. -/
theorem OpaqueProtectedValue.of_eq {t u : Term V} (h : OpaqueProtectedValue restricted t)
    (he : EqE t u) : OpaqueProtectedValue restricted u := by
  obtain ⟨v,hv,hs⟩ := h
  exact ⟨v,he.symm.trans hv,hs⟩

theorem OpaqueProtectedValue.public_subst (r : Term V) (hr : r.Public restricted)
    (σ : V → Term W) (hσ : ∀ v, OpaqueProtectedValue restricted (σ v)) :
    OpaqueProtectedValue restricted (r.subst σ) := by
  classical
  choose values he hs using hσ
  exact ⟨r.subst values,r.subst_congr _ _ he,r.opaque_safe_subst values (hr.opaque_safe r) hs⟩

theorem OpaqueProtectedValue.not_eqE_name {t : Term V} (ht : OpaqueProtectedValue restricted t)
    {name : Nat} (hn : name ∈ restricted) : ¬ EqE t (.name name) := by
  obtain ⟨u,he,hu⟩ := ht
  intro h
  exact opaque_safe_not_eqE_name hu hn (he.symm.trans h)

/-- This per-handle invariant is checked independently of public recipes. -/
def Frame.OpaqueProtected {handles : Nat} (φ : Frame restricted handles) : Prop :=
  ∀ i, OpaqueProtectedValue restricted (φ.value i)

theorem Frame.OpaqueProtected.eval {handles : Nat} {φ : Frame restricted handles}
    (hφ : φ.OpaqueProtected) (r : Recipe handles) (hr : r.Public restricted) :
    OpaqueProtectedValue restricted (φ.eval r) := OpaqueProtectedValue.public_subst r hr φ.value hφ

theorem Frame.OpaqueProtected.name_not_deducible {handles : Nat} {φ : Frame restricted handles}
    (hφ : φ.OpaqueProtected) (r : Recipe handles) (hr : r.Public restricted)
    {name : Nat} (hn : name ∈ restricted) : ¬ EqE (φ.eval r) (.name name) :=
  (hφ.eval r hr).not_eqE_name hn

end ExplainableCrypto.Helios.Symbolic
