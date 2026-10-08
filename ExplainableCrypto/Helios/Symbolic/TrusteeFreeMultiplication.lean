import ExplainableCrypto.Helios.Symbolic.TrusteeFreeValues

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type} {secret : Nat}

/-- The all-position predicate is well-defined on E0 classes. -/
def BaseClass.TrusteeFree (secret : Nat) (q : BaseClass V) : Prop :=
  ∀ t : Term V, t.baseClass = q → t.TrusteeFree secret

theorem Term.trustee_free_class (t : Term V) :
    t.baseClass.TrusteeFree secret ↔ t.TrusteeFree secret := by
  constructor
  · exact fun h => h t rfl
  · intro ht u hu
    exact ((baseClass_eq_iff _ _).mp hu).trustee_free.mpr ht

theorem Term.trustee_free_factors (t : Term V) :
    t.TrusteeFree secret ↔ ∀ q ∈ t.mulFactors, q.TrusteeFree secret := by
  induction t with
  | binary f a b ia ib =>
    cases f with
    | mul => simp only [Term.TrusteeFree, Term.mulFactors, Multiset.mem_add,
        or_imp, forall_and, ← ia, ← ib]; simp
    | _ => simpa only [Term.mulFactors, Multiset.mem_singleton, forall_eq] using
        (Term.trustee_free_class _).symm
  | _ => simpa only [Term.mulFactors, Multiset.mem_singleton, forall_eq] using
      (Term.trustee_free_class _).symm

/-- E7 retains every component, including the randomness and plaintext. -/
theorem CipherFusion.trustee_free {inputs : Multiset (BaseClass V)} {output : BaseClass V}
    (h : CipherFusion inputs output) :
    output.TrusteeFree secret ↔ ∀ q ∈ inputs, q.TrusteeFree secret := by
  obtain ⟨k, r, s, m, n, rfl, rfl⟩ := h
  simp [ciphertextPairFactors, combinedCiphertext, Term.trustee_free_class,
    Term.TrusteeFree, and_assoc, and_left_comm, and_comm]

theorem BagFusion.trustee_free {source target : Multiset (BaseClass V)}
    (h : BagFusion CipherFusion source target) :
    (∀ q ∈ source, q.TrusteeFree secret) ↔ ∀ q ∈ target, q.TrusteeFree secret := by
  obtain ⟨inputs, output, rest, h, rfl, rfl⟩ := h
  simp only [Multiset.mem_add, Multiset.mem_singleton, or_imp, forall_and, forall_eq]
  exact and_congr h.trustee_free.symm Iff.rfl

/-- Normal outer factors can only fuse; unlike erasing destructors, this path
reflects the all-position invariant as well as preserving it. -/
theorem ReducesModulo.trustee_free_iff_of_normal_factors {a b : Term V}
    (h : ReducesModulo a b) (ha : a.NormalMulFactors) :
    a.TrusteeFree secret ↔ b.TrusteeFree secret := by
  rw [a.trustee_free_factors, b.trustee_free_factors]
  have hf := (h.normal_mul_factors ha).1
  generalize a.mulFactors = source at hf ⊢
  generalize b.mulFactors = target at hf ⊢
  induction hf with
  | refl => rfl
  | tail _ hs ih => exact ih.trans hs.trustee_free

theorem TrusteeFreeValue.mul_iff (a b : Term V) :
    TrusteeFreeValue secret (.binary .mul a b) ↔
      TrusteeFreeValue secret a ∧ TrusteeFreeValue secret b := by
  constructor
  · intro h
    obtain ⟨a', ha, hna⟩ := exists_normal_form a
    obtain ⟨b', hb, hnb⟩ := exists_normal_form b
    have he := EqE.binary .mul ha.sound hb.sound
    have hn : (Term.binary .mul a' b').NormalMulFactors := by
      intro q hq
      rcases Multiset.mem_add.mp hq with hq | hq
      · exact hna.normal_mul_factors q hq
      · exact hnb.normal_mul_factors q hq
    obtain ⟨u, hp, hi⟩ := exists_normal_form (Term.binary .mul a' b')
    have hu := (h.of_eq (he.trans hp.sound)).irreducible hi
    have hf := (hp.to_modulo.trustee_free_iff_of_normal_factors hn).mpr hu
    exact ⟨⟨a', ha.sound, hf.1⟩, ⟨b', hb.sound, hf.2.1⟩⟩
  · rintro ⟨⟨a', ha, hf⟩, ⟨b', hb, hg⟩⟩
    exact ⟨.binary .mul a' b', .binary .mul ha hb, hf, hg, by simp⟩

end ExplainableCrypto.Helios.Symbolic
