import ExplainableCrypto.Helios.Symbolic.OpaqueNonDeducibility
import ExplainableCrypto.Helios.Symbolic.ComposedNonce

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type} {restricted : Finset Nat}

private theorem singleton_name_excluded (t : Term V)
    (ht : t.composeFactors = {t.baseClass}) (hs : t.opaqueSafe restricted = true)
    {n : Nat} (hn : n ∈ restricted) : (Term.name (V := V) n).baseClass ∉ t.composeFactors := by
  intro hm
  rw [ht, Multiset.mem_singleton] at hm
  have he := (baseClass_eq_iff _ _).mp hm
  rw [← he.opaque_safe] at hs
  simp [Term.opaqueSafe, hn] at hs

theorem Term.opaque_safe_no_name_factor (t : Term V) (hs : t.opaqueSafe restricted = true)
    {n : Nat} (hn : n ∈ restricted) : (Term.name (V := V) n).baseClass ∉ t.composeFactors := by
  induction t with
  | binary f a b ia ib =>
    cases f with
    | compose =>
      simp only [Term.opaqueSafe, Bool.and_eq_true] at hs
      intro hm
      rcases Multiset.mem_add.mp hm with hm | hm
      · exact ia hs.1 hm
      · exact ib hs.2 hm
    | _ => exact singleton_name_excluded _ rfl hs hn
  | _ => exact singleton_name_excluded _ rfl hs hn

/-- The target's other factors may reduce arbitrarily. Name-factor membership,
not target irreducibility, supplies the persistent contradiction at a common reduct. -/
theorem opaque_safe_not_eqE_name_factor {a b : Term V} (ha : a.opaqueSafe restricted = true)
    {n : Nat} (hn : n ∈ restricted) (hb : (Term.name (V := V) n).baseClass ∈ b.composeFactors) :
    ¬ EqE a b := by
  intro h
  obtain ⟨w, haw, hbw⟩ := (eqE_iff_join _ _).mp h
  exact w.opaque_safe_no_name_factor (haw.opaque_safe ha) hn (hbw.compose_name_mem hb)

/-- A restricted outer nonce factor remains observable at every reduct of the
target, even when its other factors are reducible. -/
theorem OpaqueProtectedValue.not_eqE_name_factor {t target : Term V}
    (ht : OpaqueProtectedValue restricted t) {name : Nat} (hn : name ∈ restricted)
    (hf : (Term.name (V := V) name).baseClass ∈ target.composeFactors) : ¬ EqE t target := by
  obtain ⟨u,he,hu⟩ := ht
  intro h
  exact opaque_safe_not_eqE_name_factor hu hn hf (he.symm.trans h)

theorem Frame.OpaqueProtected.name_factor_not_deducible {handles : Nat} {φ : Frame restricted handles}
    (hφ : φ.OpaqueProtected) (r : Recipe handles) (hr : r.Public restricted)
    {name : Nat} (hn : name ∈ restricted) (target : Ground)
    (hf : (Term.name (V := Empty) name).baseClass ∈ target.composeFactors) :
    ¬ EqE (φ.eval r) target := (hφ.eval r hr).not_eqE_name_factor hn hf

end ExplainableCrypto.Helios.Symbolic
