import ExplainableCrypto.Helios.Symbolic.TrusteeFreeReduction

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type} {secret : Nat} {restricted : Finset Nat}

/-- Public substitution is free when its handle values are free and no public
key expression can equal the designated secret. Both hypotheses matter. -/
theorem Term.Public.trustee_free_subst (r : Term V) (hr : r.Public restricted)
    (σ : V → Term W) (hσ : ∀ v, (σ v).TrusteeFree secret)
    (hsecret : ∀ t : Term V, t.Public restricted → ¬ EqE (t.subst σ) (.name secret)) :
    (r.subst σ).TrusteeFree secret := by
  induction r with
  | var v => exact hσ v
  | binary f a b ia ib =>
    exact ⟨ia hr.1, ib hr.2, fun _ => hsecret a hr.1⟩
  | _ => simp_all [Term.Public, Term.subst, Term.TrusteeFree]

theorem Term.tuple_trustee_free (xs : List (Term V))
    (h : ∀ t ∈ xs, t.TrusteeFree secret) : (Term.tuple xs).TrusteeFree secret := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    exact ⟨h x (by simp), ih (fun t ht => h t (by simp [ht])), by simp⟩

namespace Historical
variable {n : Nat}

theorem foldCandidates_trustee_free (f : Binary) (hf : f ≠ .partialDecrypt)
    (xs : Fin (n + 1) → Term V) (h : ∀ j, (xs j).TrusteeFree secret) :
    (foldCandidates f xs).TrusteeFree secret := by
  unfold foldCandidates
  generalize (List.finRange n) = rest
  have hh : (xs 0).TrusteeFree secret := h 0
  generalize xs 0 = init at hh ⊢
  induction rest generalizing init with
  | nil => exact hh
  | cons j rest ih => exact ih (.binary f init (xs j.succ)) ⟨hh, h j.succ, fun he => (hf he).elim⟩

namespace General

theorem ballot_trustee_free_bits (ns : Names n) (i : Fin 2)
    (bits : Fin (n + 1) → Constant) :
    (ballot ns i (fun j => .const (bits j))).TrusteeFree secret := by
  apply Term.tuple_trustee_free
  intro t ht
  simp only [ballotFields, List.mem_append, List.mem_map, List.mem_singleton] at ht
  rcases ht with (⟨j, _, rfl⟩ | ⟨j, _, rfl⟩) | rfl
  · trivial
  · trivial
  · refine ⟨True.intro, ?_, ?_, ?_⟩
    · exact foldCandidates_trustee_free .compose (by decide) _ (fun _ => True.intro)
    · exact foldCandidates_trustee_free .add (by decide) _ (fun _ => True.intro)
    · exact foldCandidates_trustee_free .mul (by decide) _ (fun _ => by trivial)

theorem frame_trustee_free_bits (ns : Names n) (swap : Bool) (left right : BitCandidate n) :
    ∀ h, ((frame ns swap left.substitution right.substitution).value h).TrusteeFree secret := by
  intro h
  cases swap <;> fin_cases h
  · trivial
  · exact ballot_trustee_free_bits ns 0 left.bit
  · exact ballot_trustee_free_bits ns 1 right.bit
  · trivial
  · exact ballot_trustee_free_bits ns 0 right.bit
  · exact ballot_trustee_free_bits ns 1 left.bit

/-- This inspects all nested positions, unlike name non-deducibility alone.
Candidate representatives may contain erasable secret-keyed partials. -/
theorem initial_recipe_trustee_free (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3)
    (hr : r.Public ns.restricted) :
    TrusteeFreeValue ns.secretKey ((frame ns swap left right).eval r) := by
  obtain ⟨a, b, hframe⟩ := frame_bit_representatives ns swap left right
  refine ⟨(frame ns swap a.substitution b.substitution).eval r,
    r.subst_congr _ _ hframe, ?_⟩
  apply hr.trustee_free_subst r _ (frame_trustee_free_bits ns swap a b)
  intro t ht
  exact frame_nonce_not_deducible ns swap a.substitution b.substitution t ht (by simp [Names.restricted])

end General
end Historical
end ExplainableCrypto.Helios.Symbolic
