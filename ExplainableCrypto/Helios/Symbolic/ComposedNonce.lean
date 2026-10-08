import ExplainableCrypto.Helios.Symbolic.NonceNonDeducibility

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type} {restricted : Finset Nat}

/-- An outer composition factor E0-equal to a name cannot be the reduced factor. -/
theorem ModuloStep.compose_name_mem {a b : Term V} (h : ModuloStep a b) {n : Nat}
    (hn : (Term.name (V := V) n).baseClass ∈ a.composeFactors) :
    (Term.name (V := V) n).baseClass ∈ b.composeFactors := by
  obtain ⟨x, y, rest, _, hxy, ha, hb⟩ := h.compose_factor
  rw [ha, Multiset.mem_add, Multiset.mem_singleton] at hn
  rcases hn with hn | hn
  · have hx : Irreducible x := (name_irreducible n).base ((baseClass_eq_iff _ _).mp hn)
    exact False.elim (hx y hxy)
  · rw [hb]
    exact Multiset.mem_add.mpr (Or.inr hn)

theorem ReducesModulo.compose_name_mem {a b : Term V} (h : ReducesModulo a b) {n : Nat}
    (hn : (Term.name (V := V) n).baseClass ∈ a.composeFactors) :
    (Term.name (V := V) n).baseClass ∈ b.composeFactors := by
  induction h with
  | base he => exact he.compose_factors ▸ hn
  | head hs _ ih => exact ih (hs.compose_name_mem hn)

private theorem singleton_name_excluded (t : Term V)
    (ht : t.composeFactors = {t.baseClass}) (hs : t.nonceSafe restricted = true)
    {n : Nat} (hn : n ∈ restricted) : (Term.name (V := V) n).baseClass ∉ t.composeFactors := by
  intro hm
  rw [ht, Multiset.mem_singleton] at hm
  have he := (baseClass_eq_iff _ _).mp hm
  rw [← he.nonce_safe] at hs
  simp [Term.nonceSafe, hn] at hs

theorem Term.nonce_safe_no_name_factor (t : Term V) (hs : t.nonceSafe restricted = true)
    {n : Nat} (hn : n ∈ restricted) : (Term.name (V := V) n).baseClass ∉ t.composeFactors := by
  induction t with
  | binary f a b ia ib =>
    cases f with
    | compose =>
      simp only [Term.nonceSafe, Bool.and_eq_true] at hs
      intro hm
      rcases Multiset.mem_add.mp hm with hm | hm
      · exact ia hs.1 hm
      · exact ib hs.2 hm
    | _ => exact singleton_name_excluded _ rfl hs hn
  | _ => exact singleton_name_excluded _ rfl hs hn

/-- The target's other factors may reduce arbitrarily. Name-factor membership,
not target irreducibility, supplies the persistent contradiction at a common reduct. -/
theorem nonce_safe_not_eqE_name_factor {a b : Term V} (ha : a.nonceSafe restricted = true)
    {n : Nat} (hn : n ∈ restricted) (hb : (Term.name (V := V) n).baseClass ∈ b.composeFactors) :
    ¬ EqE a b := by
  intro h
  obtain ⟨w, haw, hbw⟩ := (eqE_iff_join _ _).mp h
  exact w.nonce_safe_no_name_factor (haw.nonce_safe ha) hn (hbw.compose_name_mem hb)

theorem Frame.composed_nonce_not_deducible {handles : Nat} (φ : Frame restricted handles)
    (hφ : ∀ i, (φ.value i).nonceSafe restricted = true)
    (r : Recipe handles) (hr : r.Public restricted) {n : Nat} (hn : n ∈ restricted)
    (target : Ground) (ht : (Term.name (V := Empty) n).baseClass ∈ target.composeFactors) :
    ¬ EqE (φ.eval r) target :=
  nonce_safe_not_eqE_name_factor (r.nonce_safe_subst φ.value (hr.nonce_safe r) hφ) hn ht

theorem Frame.nonce_with_remainder_not_deducible {handles : Nat} (φ : Frame restricted handles)
    (hφ : ∀ i, (φ.value i).nonceSafe restricted = true)
    (r : Recipe handles) (hr : r.Public restricted) {n : Nat} (hn : n ∈ restricted)
    (rest : Ground) : ¬ EqE (φ.eval r) (.binary .compose (.name n) rest) := by
  apply φ.composed_nonce_not_deducible hφ r hr hn
  simp [Term.composeFactors]

end ExplainableCrypto.Helios.Symbolic
