import ExplainableCrypto.Helios.Symbolic.BagFusion
import ExplainableCrypto.Helios.Symbolic.FactorSelectionOverlap

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- E7 as a rule on an unordered pair of exact E0 ciphertext classes. -/
def CipherFusion (inputs : Multiset (BaseClass V)) (output : BaseClass V) : Prop :=
  ∃ k r s m n : Term V, inputs = ciphertextPairFactors k r s m n ∧
    output = (combinedCiphertext k r s m n).baseClass

namespace CipherFusion

theorem rank {inputs : Multiset (BaseClass V)} {output : BaseClass V}
    (h : CipherFusion inputs output) : inputs.card = 2 := by
  obtain ⟨k, r, s, m, n, rfl, _⟩ := h
  simp [ciphertextPairFactors]

theorem deterministic {inputs : Multiset (BaseClass V)} {x y : BaseClass V}
    (hx : CipherFusion inputs x) (hy : CipherFusion inputs y) : x = y := by
  obtain ⟨k, r, s, m, n, hp, rfl⟩ := hx
  obtain ⟨k', r', s', m', n', hp', rfl⟩ := hy
  have he : BaseEq (.binary .mul (.ternary .penc k r m) (.ternary .penc k s n))
      (.binary .mul (.ternary .penc k' r' m') (.ternary .penc k' s' n')) := by
    apply (baseEq_iff_mulFactors _ _).mpr
    simpa only [Term.mulFactors, ciphertextPairFactors, Multiset.singleton_add,
      Multiset.insert_eq_cons] using hp.symm.trans hp'
  exact (baseClass_eq_iff _ _).mpr (homomorphic_root_outputs_base _ _ _ _ _ _ _ _ _ _ he)

private theorem pair_matching {α : Type} {a b c d : α}
    (h : ({a, b} : Multiset α) = {c, d}) : (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hm : a = c ∨ a = d := by
    have hm : a ∈ ({c, d} : Multiset α) := by rw [← h]; simp
    simpa using hm
  rcases hm with rfl | rfl
  · exact Or.inl ⟨rfl, by simpa using h⟩
  · rw [Multiset.pair_comm c a] at h
    exact Or.inr ⟨rfl, by simpa using h⟩

/-- Orient an unordered rule instance to either specified input order. -/
theorem orient {a b output : BaseClass V} (h : CipherFusion {a, b} output) :
    ∃ k r s m n : Term V,
      a = (Term.ternary .penc k r m).baseClass ∧
      b = (Term.ternary .penc k s n).baseClass ∧
      output = (combinedCiphertext k r s m n).baseClass := by
  obtain ⟨k, r, s, m, n, hp, ho⟩ := h
  rcases pair_matching hp with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact ⟨k, r, s, m, n, ha, hb, ho⟩
  · refine ⟨k, s, r, n, m, ha, hb, ho.trans ?_⟩
    apply (baseClass_eq_iff _ _).mpr
    exact .ternary .penc (.refl _) (.equation (.comm .compose trivial _ _))
      (.equation (.comm .add trivial _ _))

/-- Shared ciphertext equality supplies key/nonce/plaintext alignment. The rule
association law is proved for exact quotient classes, with no confluence premise. -/
theorem associate {a b c x y : BaseClass V}
    (hx : CipherFusion {a, b} x) (hy : CipherFusion {b, c} y) :
    ∃ z, CipherFusion {x, c} z ∧ CipherFusion {a, y} z := by
  obtain ⟨k, r, s, m, n, ha, hb, hx⟩ := orient hx
  obtain ⟨l, t, u, p, q, hb', hc, hy⟩ := orient hy
  have hcommon := (baseClass_eq_iff _ _).mp (hb.symm.trans hb')
  obtain ⟨hkl, hst, hnp⟩ := (BaseEq.penc_iff _ _ _ _ _ _).mp hcommon
  have hc' : c = (Term.ternary .penc k u q).baseClass := hc.trans
    ((baseClass_eq_iff _ _).mpr (.ternary .penc hkl.symm (.refl _) (.refl _)))
  have hy' : y = (combinedCiphertext k s u n q).baseClass := hy.trans
    ((baseClass_eq_iff _ _).mpr (.ternary .penc hkl.symm
      (.binary .compose hst.symm (.refl _)) (.binary .add hnp.symm (.refl _))))
  refine ⟨(tripleFinalLeft k r s u m n q).baseClass, ?_, ?_⟩
  · refine ⟨k, .binary .compose r s, u, .binary .add m n, q, ?_, rfl⟩
    rw [hx, hc']
  · refine ⟨k, r, .binary .compose s u, m, .binary .add n q, ?_, ?_⟩
    · rw [ha, hy']
    · exact (baseClass_eq_iff _ _).mpr (triple_endpoints_base k r s u m n q)

end CipherFusion

/-- Exhaustive fusion diamond: all three bag-selection cases use proved E7 laws. -/
theorem cipher_fusion_diamond {source u v : Multiset (BaseClass V)}
    (hu : BagFusion CipherFusion source u) (hv : BagFusion CipherFusion source v) :
    u = v ∨ ∃ w, BagFusion CipherFusion u w ∧ BagFusion CipherFusion v w :=
  bag_fusion_diamond CipherFusion (fun _ _ h => h.rank)
    (fun _ _ _ hx hy => hx.deterministic hy)
    (fun _ _ _ _ _ hx hy => hx.associate hy) hu hv

/-- Fusion of two outer ciphertext factors. This does not include internal factor rewrites. -/
def OuterFusion (a b : Term V) : Prop := BagFusion CipherFusion a.mulFactors b.mulFactors

theorem OuterFusion.of_factors (a b k r s m n : Term V) (rest : Multiset (BaseClass V))
    (ha : a.mulFactors = ciphertextPairFactors k r s m n + rest)
    (hb : b.mulFactors = {(combinedCiphertext k r s m n).baseClass} + rest) :
    OuterFusion a b :=
  ⟨_, _, rest, ⟨k, r, s, m, n, rfl, rfl⟩, ha, hb⟩

theorem OuterFusion.card_step {a b : Term V} (h : OuterFusion a b) :
    a.mulFactors.card = b.mulFactors.card + 1 := by
  obtain ⟨inputs, output, rest, hr, hs, ht⟩ := h
  have hs' := congrArg Multiset.card hs
  have ht' := congrArg Multiset.card ht
  have hrank := hr.rank
  simp only [Multiset.card_add, Multiset.card_singleton] at hs' ht'
  omega

/-- Every abstract fusion target is represented by an actual modulo-step endpoint. -/
theorem realize_cipher_fusion (a : Term V) {target : Multiset (BaseClass V)}
    (h : BagFusion CipherFusion a.mulFactors target) :
    ∃ b, ModuloStep a b ∧ b.mulFactors = target := by
  obtain ⟨inputs, output, rest, hr, hs, ht⟩ := h
  obtain ⟨k, r, s, m, n, hp, ho⟩ := hr
  have hs' : a.mulFactors = ciphertextPairFactors k r s m n + rest := by simpa only [hp] using hs
  obtain ⟨b, hab, hb⟩ := homomorphic_selection_reachable a k r s m n rest hs'
  have ht' : target = {(combinedCiphertext k r s m n).baseClass} + rest := by simpa only [ho] using ht
  exact ⟨b, hab, hb.trans ht'.symm⟩

theorem OuterFusion.to_modulo {a b : Term V} (h : OuterFusion a b) : ModuloStep a b := by
  obtain ⟨b', hab', hb'⟩ := realize_cipher_fusion a h
  exact hab'.post_base ((baseEq_iff_mulFactors _ _).mpr hb')

/-- Arbitrary specified outer fusion witnesses join, including repeated factors
and different E0 representatives. No selection-case or matching premise remains. -/
theorem outer_fusion_peak_joined {a b c : Term V}
    (hb : OuterFusion a b) (hc : OuterFusion a c) :
    ModuloStep a b ∧ ModuloStep a c ∧ JoinModulo b c := by
  refine ⟨hb.to_modulo, hc.to_modulo, ?_⟩
  rcases cipher_fusion_diamond hb hc with he | ⟨factors, hbf, hcf⟩
  · exact ⟨c, .base ((baseEq_iff_mulFactors _ _).mpr he), .refl _⟩
  · obtain ⟨d, hbd, hd⟩ := realize_cipher_fusion b hbf
    have hcd : OuterFusion c d := by
      unfold OuterFusion
      simpa only [hd] using hcf
    exact ⟨d, .single hbd, .single hcd.to_modulo⟩

end ExplainableCrypto.Helios.Symbolic
