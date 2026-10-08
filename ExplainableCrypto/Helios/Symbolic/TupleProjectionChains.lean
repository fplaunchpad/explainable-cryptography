import ExplainableCrypto.Helios.Symbolic.TupleProjectionPaths
import ExplainableCrypto.Helios.Symbolic.HistoricalCiphertextProducts

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type}

/-- A syntax predicate for fst/snd chains rooted at one supplied handle.
It adds no operation to the public term language. -/
inductive ProjectionChain (v : V) : Term V → Prop where
  | handle : ProjectionChain v (.var v)
  | step (f : Unary) (hf : f = .fst ∨ f = .snd) {r : Term V}
      (h : ProjectionChain v r) : ProjectionChain v (.unary f r)

theorem ProjectionChain.drop (v : V) (n : Nat) : ProjectionChain v ((Term.var v).drop n) := by
  induction n with
  | zero => exact .handle
  | succ n ih => rw [Term.drop_succ_outer]; exact .step .snd (Or.inr rfl) ih

theorem ProjectionChain.project (v : V) (n : Nat) : ProjectionChain v ((Term.var v).project n) :=
  .step .fst (Or.inl rfl) (.drop v n)

theorem ProjectionChain.isPublic {v : V} {r : Term V} (h : ProjectionChain v r)
    (restricted : Finset Nat) : r.Public restricted := by
  induction h with
  | handle => trivial
  | step f hf h ih => exact ih

theorem ProjectionChain.not_pair_of_handle {σ : V → Term W} {v : V} {r : Term V}
    (h : ProjectionChain v r) (hv : ∀ x y, ¬ EqE (σ v) (.binary .pair x y))
    (x y : Term W) : ¬ EqE (r.subst σ) (.binary .pair x y) := by
  induction h generalizing x y with
  | handle => exact hv x y
  | step f hf h ih =>
    intro he
    obtain ⟨p, q, hp, _⟩ := he.projection_pair_inversion hf
    exact ih p q hp.sound

theorem ProjectionChain.not_ciphertext_of_handle {σ : V → Term W} {v : V} {r : Term V}
    (h : ProjectionChain v r) (hp : ∀ x y, ¬ EqE (σ v) (.binary .pair x y))
    (hv : ∀ k s m, ¬ EqE (σ v) (.ternary .penc k s m))
    (k s m : Term W) : ¬ EqE (r.subst σ) (.ternary .penc k s m) := by
  cases h with
  | handle => exact hv k s m
  | step f hf h =>
    intro he
    obtain ⟨p, q, hpair, _⟩ := he.projection_penc_inversion hf
    exact h.not_pair_of_handle hp p q hpair.sound

/-- An E-valued finite tuple with non-pair fields can expose pairs only as valid tails. -/
theorem ProjectionChain.pair_origin {σ : V → Term W} {v : V} {r : Term V}
    (h : ProjectionChain v r) (xs : List (Term W)) (hv : EqE (σ v) (Term.tuple xs))
    (hf : ∀ t ∈ xs, ∀ x y, ¬ EqE t (.binary .pair x y))
    {x y : Term W} (he : EqE (r.subst σ) (.binary .pair x y)) :
    ∃ i, i < xs.length ∧ r = (Term.var v).drop i := by
  induction h generalizing x y with
  | handle => exact ⟨0, tuple_eqE_pair_nonempty xs (hv.symm.trans he), rfl⟩
  | @step f hfn r h ih =>
    obtain ⟨p, q, hp, hout⟩ := he.projection_pair_inversion hfn
    obtain ⟨i, hi, rfl⟩ := ih hp.sound
    rcases hfn with rfl | rfl
    · have hs : EqE (((Term.var v : Term V).project i).subst σ) xs[i] := by
        rw [Term.subst_project]
        exact (EqE.unary .fst (hv.drop i)).trans (project_tuple_get xs i hi)
      exact False.elim (hf xs[i] (List.getElem_mem hi) x y (hs.symm.trans he))
    · have hle : i + 1 ≤ xs.length := by omega
      have hs : EqE ((Term.unary .snd ((Term.var v).drop i) : Term V).subst σ)
          (Term.tuple (xs.drop (i + 1))) := by
        rw [← Term.drop_succ_outer, Term.subst_drop]
        exact (hv.drop (i + 1)).trans (tuple_drop_reduces xs (i + 1) hle).sound
      have hpos := tuple_eqE_pair_nonempty (xs.drop (i + 1)) (hs.symm.trans he)
      simp only [List.length_drop] at hpos
      exact ⟨i + 1, by omega, (Term.drop_succ_outer i (.var v)).symm⟩

/-- A ciphertext-valued chain selects exactly one valid tuple field. The raw
recipe equality preserves the indexed-selector exception, not just its E-value. -/
theorem ProjectionChain.ciphertext_origin {σ : V → Term W} {v : V} {r : Term V}
    (h : ProjectionChain v r) (xs : List (Term W)) (hv : EqE (σ v) (Term.tuple xs))
    (hf : ∀ t ∈ xs, ∀ x y, ¬ EqE t (.binary .pair x y))
    {k s m : Term W} (he : EqE (r.subst σ) (.ternary .penc k s m)) :
    ∃ i, ∃ hi : i < xs.length, r = (Term.var v).project i ∧ EqE xs[i] (.ternary .penc k s m) := by
  cases h with
  | handle => exact False.elim (tuple_not_eqE_penc xs k s m (hv.symm.trans he))
  | step f hfn h =>
    obtain ⟨p, q, hp, _⟩ := he.projection_penc_inversion hfn
    obtain ⟨i, hi, rfl⟩ := h.pair_origin xs hv hf hp.sound
    rcases hfn with rfl | rfl
    · refine ⟨i, hi, rfl, ?_⟩
      have hs : EqE (((Term.var v : Term V).project i).subst σ) xs[i] := by
        rw [Term.subst_project]
        exact (EqE.unary .fst (hv.drop i)).trans (project_tuple_get xs i hi)
      exact hs.symm.trans he
    · have hs : EqE ((Term.unary .snd ((Term.var v).drop i) : Term V).subst σ)
          (Term.tuple (xs.drop (i + 1))) := by
        rw [← Term.drop_succ_outer, Term.subst_drop]
        exact (hv.drop (i + 1)).trans (tuple_drop_reduces xs (i + 1) (by omega)).sound
      exact False.elim (tuple_not_eqE_penc _ k s m (hs.symm.trans he))

theorem ProjectionChain.proof_origin {σ : V → Term W} {v : V} {r : Term V}
    (h : ProjectionChain v r) (xs : List (Term W)) (hv : EqE (σ v) (Term.tuple xs))
    (hf : ∀ t ∈ xs, ∀ x y, ¬ EqE t (.binary .pair x y))
    {k s m c : Term W} (he : EqE (r.subst σ) (.spk k s m c)) :
    ∃ i, ∃ hi : i < xs.length, r = (Term.var v).project i ∧ EqE xs[i] (.spk k s m c) := by
  cases h with
  | handle => exact False.elim (tuple_not_eqE_spk xs k s m c (hv.symm.trans he))
  | step f hfn h =>
    obtain ⟨p, q, hp, _⟩ := he.projection_spk_inversion hfn
    obtain ⟨i, hi, rfl⟩ := h.pair_origin xs hv hf hp.sound
    rcases hfn with rfl | rfl
    · refine ⟨i, hi, rfl, ?_⟩
      have hs : EqE (((Term.var v : Term V).project i).subst σ) xs[i] := by
        rw [Term.subst_project]
        exact (EqE.unary .fst (hv.drop i)).trans (project_tuple_get xs i hi)
      exact hs.symm.trans he
    · have hs : EqE ((Term.unary .snd ((Term.var v).drop i) : Term V).subst σ)
          (Term.tuple (xs.drop (i + 1))) := by
        rw [← Term.drop_succ_outer, Term.subst_drop]
        exact (hv.drop (i + 1)).trans (tuple_drop_reduces xs (i + 1) (by omega)).sound
      exact False.elim (tuple_not_eqE_spk _ k s m c (hs.symm.trans he))

end ExplainableCrypto.Helios.Symbolic
