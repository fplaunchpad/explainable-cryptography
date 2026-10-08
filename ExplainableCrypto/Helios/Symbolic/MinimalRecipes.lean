import ExplainableCrypto.Helios.Symbolic.RawNormalization
import Mathlib.Data.Nat.Find

/-! Minimum raw syntax size among public recipes with the same substituted E-value.
The variable type fixes the available handles. This is a logical definition,
not an equality decision procedure or a modulo-E0 normalization algorithm. -/
namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type} {restricted : Finset Nat} {σ : V → Term W}

theorem Term.nodeCount_pos (t : Term V) : 0 < t.nodeCount := by
  cases t <;> simp only [Term.nodeCount] <;> omega

theorem Context.nodeCount_balance (c : Context V) (a b : Term V) :
    (c.fill a).nodeCount + b.nodeCount = (c.fill b).nodeCount + a.nodeCount := by
  induction c <;> simp_all [Context.fill, Term.nodeCount] <;> omega

theorem Context.nodeCount_lt_iff (c : Context V) (a b : Term V) :
    (c.fill a).nodeCount < (c.fill b).nodeCount ↔ a.nodeCount < b.nodeCount := by
  have := c.nodeCount_balance a b
  omega

theorem Context.public_hole (c : Context V) {a : Term V}
    (h : (c.fill a).Public restricted) : a.Public restricted := by
  induction c <;> simp_all [Context.fill, Term.Public]

theorem Context.public_replace (c : Context V) {a b : Term V}
    (h : (c.fill a).Public restricted) (hb : b.Public restricted) :
    (c.fill b).Public restricted := by
  induction c <;> simp_all [Context.fill, Term.Public]

theorem RootStep.nodeCount_lt {a b : Term V} (h : RootStep a b) :
    b.nodeCount < a.nodeCount := by
  cases h <;> simp only [Term.nodeCount]
  all_goals first | omega | (rename_i k _ _ _ _; have := k.nodeCount_pos; omega)

theorem RewriteStep.nodeCount_lt {a b : Term V} (h : RewriteStep a b) :
    b.nodeCount < a.nodeCount := by
  obtain ⟨c, l, r, h, rfl, rfl⟩ := h
  exact (c.nodeCount_lt_iff r l).2 h.nodeCount_lt

theorem RootStep.public {a b : Term V} (h : RootStep a b)
    (ha : a.Public restricted) : b.Public restricted := by
  cases h <;> simp_all [Term.Public]

theorem RewriteStep.public {a b : Term V} (h : RewriteStep a b)
    (ha : a.Public restricted) : b.Public restricted := by
  obtain ⟨c, l, r, h, rfl, rfl⟩ := h
  exact c.public_replace ha (h.public (c.public_hole ha))

/-- Minimum among all public recipes over this handle type and substitution. -/
structure MinimalRecipe (restricted : Finset Nat) (σ : V → Term W) (r : Term V) : Prop where
  isPublic : r.Public restricted
  least : ∀ s : Term V, s.Public restricted →
    EqE (r.subst σ) (s.subst σ) → r.nodeCount ≤ s.nodeCount

/-- Existence retains the input's public-name policy and substituted E-value. -/
theorem exists_minimal_recipe (r : Term V) (hr : r.Public restricted) :
    ∃ s, MinimalRecipe restricted σ s ∧ EqE (r.subst σ) (s.subst σ) := by
  classical
  let p : Nat → Prop := fun k => ∃ s : Term V,
    s.Public restricted ∧ EqE (r.subst σ) (s.subst σ) ∧ s.nodeCount = k
  have hp : ∃ k, p k := ⟨r.nodeCount, r, hr, .refl _, rfl⟩
  obtain ⟨s, hs, he, hsize⟩ := Nat.find_spec hp
  refine ⟨s, ⟨hs, ?_⟩, he⟩
  intro t ht het
  rw [hsize]
  exact Nat.find_min' hp ⟨t, ht, he.trans het, rfl⟩

namespace MinimalRecipe
variable {r s : Term V}

/-- Any actual smaller public equivalent refutes minimality. -/
theorem no_smaller (h : MinimalRecipe restricted σ r) (hs : s.Public restricted)
    (he : EqE (r.subst σ) (s.subst σ)) (hlt : s.nodeCount < r.nodeCount) : False :=
  (Nat.not_lt_of_ge (h.least s hs he)) hlt

/-- Minimality is inherited by every one-hole syntactic subterm. -/
theorem subterm (c : Context V) (h : MinimalRecipe restricted σ (c.fill r)) :
    MinimalRecipe restricted σ r := by
  refine ⟨c.public_hole h.isPublic, ?_⟩
  intro s hs he
  have hc : EqE ((c.fill r).subst σ) ((c.fill s).subst σ) := by
    simpa only [Context.subst_fill] using (c.subst σ).congr he
  have hle := h.least (c.fill s) (c.public_replace h.isPublic hs) hc
  have hbalance := c.nodeCount_balance r s
  omega

/-- Ordinary rewriting shrinks syntax and preserves publicness before substitution. -/
theorem raw_irreducible (h : MinimalRecipe restricted σ r) : RawIrreducible r := by
  intro s hs
  exact h.no_smaller (hs.public h.isPublic) (hs.sound.subst σ) hs.nodeCount_lt

/-- Atomic public recipes attain the lower bound on syntax size. -/
theorem of_nodeCount_one (hr : r.Public restricted) (hn : r.nodeCount = 1) :
    MinimalRecipe restricted σ r := by
  refine ⟨hr, fun s _ _ => ?_⟩
  have := s.nodeCount_pos
  omega

/-- Semantic key matching suffices; the keys need not be syntactically equal. -/
theorem not_decrypt_ciphertext (k key nonce m : Term V)
    (hkey : EqE (key.subst σ) (.unary .pk (k.subst σ))) :
    ¬ MinimalRecipe restricted σ (.binary .dec k (.ternary .penc key nonce m)) := by
  intro h
  have hm : m.Public restricted := h.isPublic.2.2.2
  have he : EqE ((.binary .dec k (.ternary .penc key nonce m) : Term V).subst σ)
      (m.subst σ) :=
    (EqE.binary .dec (.refl _) (.ternary .penc hkey (.refl _) (.refl _))).trans
      (RootStep.decrypt _ _ _).sound
  apply h.no_smaller hm he
  simp only [Term.nodeCount]
  omega

/-- E7 can remove a key copy even when the two key recipes match only semantically. -/
theorem not_ciphertext_product (key key' r s m n : Term V)
    (hkey : EqE (key'.subst σ) (key.subst σ)) :
    ¬ MinimalRecipe restricted σ
      (.binary .mul (.ternary .penc key r m) (.ternary .penc key' s n)) := by
  intro h
  let t : Term V := .ternary .penc key (.binary .compose r s) (.binary .add m n)
  have ht : t.Public restricted :=
    ⟨h.isPublic.1.1, ⟨h.isPublic.1.2.1, h.isPublic.2.2.1⟩,
      ⟨h.isPublic.1.2.2, h.isPublic.2.2.2⟩⟩
  have he : EqE
      ((.binary .mul (.ternary .penc key r m) (.ternary .penc key' s n) : Term V).subst σ)
      (t.subst σ) :=
    (EqE.binary .mul (.refl _) (.ternary .penc hkey (.refl _) (.refl _))).trans
      (RootStep.homomorphic _ _ _ _ _).sound
  apply h.no_smaller ht he
  have := key'.nodeCount_pos
  simp only [t, Term.nodeCount]
  omega

/-- E6 matching may arise only after evaluation; the exposed plaintext still shortens. -/
theorem not_partial_decryption (k key nonce m ciphertext : Term V)
    (hkey : EqE (key.subst σ) (.unary .pk (k.subst σ)))
    (hc : EqE (ciphertext.subst σ) ((.ternary .penc key nonce m : Term V).subst σ)) :
    ¬ MinimalRecipe restricted σ
      (.binary .dec (.binary .partialDecrypt k (.ternary .penc key nonce m)) ciphertext) := by
  intro h
  have hm : m.Public restricted := h.isPublic.1.2.2.2
  have hp : EqE ((.ternary .penc key nonce m : Term V).subst σ)
      (.ternary .penc (.unary .pk (k.subst σ)) (nonce.subst σ) (m.subst σ)) :=
    .ternary .penc hkey (.refl _) (.refl _)
  have he : EqE
      ((.binary .dec (.binary .partialDecrypt k (.ternary .penc key nonce m)) ciphertext : Term V).subst σ)
      (m.subst σ) :=
    (EqE.binary .dec (.binary .partialDecrypt (.refl _) hp) (hc.trans hp)).trans
      (RootStep.partial_decrypt _ _ _).sound
  apply h.no_smaller hm he
  simp only [Term.nodeCount]
  omega

end MinimalRecipe
end ExplainableCrypto.Helios.Symbolic
