import ExplainableCrypto.Helios.Symbolic.MinimumMultiplicationOrigins

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Normality is a property of the existing E0 class, not of a selected encoding. -/
def BaseClass.Normal (q : BaseClass V) : Prop :=
  ∃ t : Term V, t.baseClass = q ∧ Irreducible t

/-- Each outer multiplication factor has a modulo-irreducible representative.
The product may still admit ciphertext fusion between these factors. -/
def Term.NormalMulFactors (t : Term V) : Prop :=
  ∀ q ∈ t.mulFactors, q.Normal

theorem BaseClass.Normal.irreducible {t : Term V} (h : t.baseClass.Normal) : Irreducible t := by
  obtain ⟨u, hu, hn⟩ := h
  exact hn.base ((baseClass_eq_iff _ _).mp hu)

theorem Irreducible.normal_mul_factors {t : Term V} (ht : Irreducible t) : t.NormalMulFactors := by
  intro q hq
  induction t with
  | binary f a b ia ib =>
    cases f with
    | mul =>
      rcases Multiset.mem_add.mp hq with hq | hq
      · exact ia (ht.context_hole (.binaryLeft .mul .hole b)) hq
      · exact ib (ht.context_hole (.binaryRight .mul a .hole)) hq
    | _ => exact ⟨_, (Multiset.mem_singleton.mp hq).symm, ht⟩
  | _ => exact ⟨_, (Multiset.mem_singleton.mp hq).symm, ht⟩

/-- A ciphertext is irreducible when all three of its components are. -/
theorem Irreducible.penc {k r m : Term V} (hk : Irreducible k)
    (hr : Irreducible r) (hm : Irreducible m) : Irreducible (.ternary .penc k r m) := by
  intro t hs
  rcases hs.penc_cases with ⟨k', h, _⟩ | ⟨r', h, _⟩ | ⟨m', h, _⟩
  · exact hk k' h
  · exact hr r' h
  · exact hm m' h

/-- Fusing normal ciphertext factors produces a normal ciphertext factor:
composition and addition of normal components remain normal modulo E0. -/
theorem CipherFusion.normal_output {inputs : Multiset (BaseClass V)} {output : BaseClass V}
    (h : CipherFusion inputs output) (hi : ∀ q ∈ inputs, q.Normal) : output.Normal := by
  obtain ⟨k, r, s, m, n, rfl, rfl⟩ := h
  have ha : Irreducible (Term.ternary .penc k r m) :=
    (hi _ (by simp [ciphertextPairFactors])).irreducible
  have hb : Irreducible (Term.ternary .penc k s n) :=
    (hi _ (by simp [ciphertextPairFactors])).irreducible
  have hk := ha.context_hole (.ternaryFirst .penc .hole r m)
  have hr := ha.context_hole (.ternarySecond .penc k .hole m)
  have hs := hb.context_hole (.ternarySecond .penc k .hole n)
  have hm := ha.context_hole (.ternaryThird .penc k r .hole)
  have hn := hb.context_hole (.ternaryThird .penc k s .hole)
  exact ⟨_, rfl, hk.penc (hr.compose hs) (hm.add hn)⟩

/-- Every step out of a product of normal factors is an outer fusion. Internal
factor steps are impossible, and the resulting factors remain normal. -/
theorem ModuloStep.normal_mul_factors {a b : Term V} (hs : ModuloStep a b)
    (ha : a.NormalMulFactors) : OuterFusion a b ∧ b.NormalMulFactors := by
  rcases hs.factor_cases with hf | hi
  · refine ⟨hf, ?_⟩
    obtain ⟨inputs, output, rest, h, he, he'⟩ := hf
    have hn : output.Normal := h.normal_output (by
      intro q hq
      exact ha q (by rw [he]; exact Multiset.mem_add.mpr (Or.inl hq)))
    intro q hq
    rw [he'] at hq
    rcases Multiset.mem_add.mp hq with hq | hq
    · exact (Multiset.mem_singleton.mp hq) ▸ hn
    · exact ha q (by rw [he]; exact Multiset.mem_add.mpr (Or.inr hq))
  · obtain ⟨x, y, rest, _, hxy, he, _⟩ := hi
    have hx : Irreducible x := (ha x.baseClass (by rw [he]; simp)).irreducible
    exact False.elim (hx y hxy)

/-- Actual modulo paths from normal factor families induce only ciphertext
fusion paths on their bags. No internal factor rewrite is silently ignored. -/
theorem ReducesModulo.normal_mul_factors {a b : Term V} (hs : ReducesModulo a b)
    (ha : a.NormalMulFactors) :
    Relation.ReflTransGen (BagFusion CipherFusion) a.mulFactors b.mulFactors ∧ b.NormalMulFactors := by
  revert ha
  induction hs with
  | base he =>
    intro ha
    refine ⟨?_, ?_⟩
    · rw [he.mul_factors]
    · intro q hq
      exact ha q (by simpa only [he.mul_factors] using hq)
  | head hstep _ ih =>
    intro ha
    have hm := hstep.normal_mul_factors ha
    have ht := ih hm.2
    exact ⟨(Relation.ReflTransGen.single (show BagFusion CipherFusion _ _ from hm.1)).trans ht.1, ht.2⟩

/-- Normalizing a product of normal factors requires only outer fusion at the
factor-bag level. The normal endpoint and its actual path are retained. -/
theorem exists_normal_form_by_fusion (t : Term V) (ht : t.NormalMulFactors) :
    ∃ u, Irreducible u ∧ ReducesModulo t u ∧
      Relation.ReflTransGen (BagFusion CipherFusion) t.mulFactors u.mulFactors := by
  obtain ⟨u, hu, hn⟩ := exists_normal_form t
  exact ⟨u, hn, hu.to_modulo, (hu.to_modulo.normal_mul_factors ht).1⟩

/-- Every finite abstract fusion path has an actual term-level modulo path
with exactly the requested final bag. -/
theorem realize_cipher_fusion_path (t : Term V) {bag : Multiset (BaseClass V)}
    (h : Relation.ReflTransGen (BagFusion CipherFusion) t.mulFactors bag) :
    ∃ u, ReducesModulo t u ∧ u.mulFactors = bag := by
  generalize he : t.mulFactors = source at h
  induction h generalizing t with
  | refl => exact ⟨t, .refl _, he⟩
  | tail _ hs ih =>
    obtain ⟨u, hu, he'⟩ := ih t he
    obtain ⟨v, hv, hb⟩ := realize_cipher_fusion u (by simpa only [he'] using hs)
    exact ⟨v, hu.trans (.single hv), hb⟩

/-- Equality of products of normal factors is exactly joinability of their
factor bags by ciphertext fusion. Raw bag equality would be too strong. -/
theorem eqE_iff_normal_fusion_join (a b : Term V)
    (ha : a.NormalMulFactors) (hb : b.NormalMulFactors) :
    EqE a b ↔ ∃ bag, Relation.ReflTransGen (BagFusion CipherFusion) a.mulFactors bag ∧
      Relation.ReflTransGen (BagFusion CipherFusion) b.mulFactors bag := by
  constructor
  · intro he
    obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp he
    exact ⟨w.mulFactors, (hl.normal_mul_factors ha).1, (hr.normal_mul_factors hb).1⟩
  · rintro ⟨bag, hl, hr⟩
    obtain ⟨u, hu, heu⟩ := realize_cipher_fusion_path a hl
    obtain ⟨v, hv, hev⟩ := realize_cipher_fusion_path b hr
    exact hu.sound.trans (((baseEq_iff_mulFactors _ _).mpr (heu.trans hev.symm)).sound.trans hv.sound.symm)

/-- With normal factors, excluding outer fusion excludes every modulo step. -/
theorem irreducible_of_normal_mul_factors (t : Term V) (ht : t.NormalMulFactors)
    (hf : ∀ u, ¬ OuterFusion t u) : Irreducible t := by
  intro u hu
  exact hf u (hu.normal_mul_factors ht).1

/-- A normal term with a multiplication head cannot also be a ciphertext value. -/
theorem Irreducible.mul_not_ciphertext {a b : Term V} (ht : Irreducible (.binary .mul a b)) :
    ¬ (Term.binary .mul a b).CiphertextValue := by
  rintro ⟨k, r, m, he⟩
  obtain ⟨_, _, _, bad, _⟩ := he.symm.penc_irreducible_shape ht
  cases bad

end ExplainableCrypto.Helios.Symbolic
