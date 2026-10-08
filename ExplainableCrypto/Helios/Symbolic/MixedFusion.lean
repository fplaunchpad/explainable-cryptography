import ExplainableCrypto.Helios.Symbolic.CiphertextStep
import ExplainableCrypto.Helios.Symbolic.FactorReduction

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- A single outer factor reduces, possibly expanding to several outer factors.
The representative source is required to have exactly its singleton factor bag. -/
def FactorStep (source target : Term V) : Prop :=
  ∃ a b : Term V, ∃ rest : Multiset (BaseClass V),
    a.mulFactors = {a.baseClass} ∧ ModuloStep a b ∧
    source.mulFactors = {a.baseClass} + rest ∧ target.mulFactors = b.mulFactors + rest

theorem FactorStep.to_modulo {source target : Term V}
    (h : FactorStep source target) : ModuloStep source target := by
  obtain ⟨a, b, rest, ha, hab, hs, ht⟩ := h
  exact hab.of_factors rest (by simpa only [ha] using hs) ht

/-- A specified selected ciphertext may undergo any modulo step; all other
outer factors are retained in the two specified branch bags. -/
theorem selected_ciphertext_fusion_joined (source u v k r s m n t : Term V)
    (rest : Multiset (BaseClass V))
    (ht : ModuloStep (.ternary .penc k r m) t)
    (hs : source.mulFactors = ciphertextPairFactors k r s m n + rest)
    (hu : u.mulFactors = {(combinedCiphertext k r s m n).baseClass} + rest)
    (hv : v.mulFactors = t.mulFactors +
      ({(Term.ternary .penc k s n).baseClass} + rest)) :
    ModuloStep source u ∧ ModuloStep source v ∧ JoinModulo u v := by
  refine ⟨(OuterFusion.of_factors _ _ k r s m n rest hs hu).to_modulo, ?_, ?_⟩
  · apply ht.of_factors ({(Term.ternary .penc k s n).baseClass} + rest) _ hv
    simpa only [Term.mulFactors, ciphertextPairFactors, Multiset.insert_eq_cons,
      Multiset.cons_add, Multiset.singleton_add] using hs
  · apply (fusion_ciphertext_peak_joined k r s m n ht).of_factors rest
    · simpa only [Term.mulFactors] using hu
    · simpa only [Term.mulFactors, Multiset.add_assoc] using hv

/-- A reduction in a disjoint subproduct commutes with fusion. Its output may
have any nonempty factor bag, rather than being forced to remain one factor. -/
theorem disjoint_fusion_reduction_joined (source u v k r s m n a b : Term V)
    (rest : Multiset (BaseClass V)) (hab : ModuloStep a b)
    (hs : source.mulFactors = ciphertextPairFactors k r s m n + (a.mulFactors + rest))
    (hu : u.mulFactors = {(combinedCiphertext k r s m n).baseClass} + (a.mulFactors + rest))
    (hv : v.mulFactors = ciphertextPairFactors k r s m n + (b.mulFactors + rest)) :
    ModuloStep source u ∧ ModuloStep source v ∧ JoinModulo u v := by
  let pair : Term V := .binary .mul (.ternary .penc k r m) (.ternary .penc k s n)
  let combined := combinedCiphertext k r s m n
  have hjoin : JoinModulo (.binary .mul combined a) (.binary .mul pair b) :=
    ⟨.binary .mul combined b,
      .single (hab.context (.binaryRight .mul combined .hole)),
      .single ((RootStep.homomorphic k r s m n).to_modulo.context (.binaryLeft .mul .hole b))⟩
  refine ⟨(OuterFusion.of_factors _ _ k r s m n _ hs hu).to_modulo, ?_, ?_⟩
  · apply (hab.context (.binaryRight .mul pair .hole)).of_factors rest
    · simpa only [Context.fill, pair, Term.mulFactors, ciphertextPairFactors,
        Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add,
        Multiset.add_assoc] using hs
    · simpa only [Context.fill, pair, Term.mulFactors, ciphertextPairFactors,
        Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add,
        Multiset.add_assoc] using hv
  · apply hjoin.of_factors rest
    · simpa only [combined, Term.mulFactors, Multiset.add_assoc] using hu
    · simpa only [pair, Term.mulFactors, ciphertextPairFactors, Multiset.insert_eq_cons,
        Multiset.cons_add, Multiset.singleton_add, Multiset.add_assoc] using hv

/-- Orient the rule around a specified member, including repeated equal factors. -/
theorem CipherFusion.orient_member {inputs : Multiset (BaseClass V)} {output x : BaseClass V}
    (h : CipherFusion inputs output) (hx : x ∈ inputs) :
    ∃ k r s m n : Term V,
      x = (Term.ternary .penc k r m).baseClass ∧
      inputs = ciphertextPairFactors k r s m n ∧
      output = (combinedCiphertext k r s m n).baseClass := by
  obtain ⟨k, r, s, m, n, rfl, ho⟩ := h
  simp only [ciphertextPairFactors, Multiset.insert_eq_cons, Multiset.mem_cons,
    Multiset.mem_singleton] at hx
  rcases hx with hx | hx
  · exact ⟨k, r, s, m, n, hx, rfl, ho⟩
  · refine ⟨k, s, r, n, m, hx, Multiset.pair_comm _ _, ho.trans ?_⟩
    exact (baseClass_eq_iff _ _).mpr (.ternary .penc (.refl _)
      (.equation (.comm .compose trivial _ _)) (.equation (.comm .add trivial _ _)))

/-- Every outer fusion competes joinably with every single-factor modulo step.
This classifies selected versus disjoint factor occurrences; it does not yet
classify arbitrary modulo steps as fusion or single-factor steps. -/
theorem fusion_factor_peak_joined {source u v : Term V}
    (hf : OuterFusion source u) (hi : FactorStep source v) :
    ModuloStep source u ∧ ModuloStep source v ∧ JoinModulo u v := by
  refine ⟨hf.to_modulo, hi.to_modulo, ?_⟩
  obtain ⟨inputs, output, rest, hrule, hs, hu⟩ := hf
  obtain ⟨a, b, residual, ha, hab, hs', hv⟩ := hi
  have hmem : a.baseClass ∈ inputs + rest := by
    rw [← hs, hs']
    simp
  rcases Multiset.mem_add.mp hmem with hin | hout
  · obtain ⟨k, r, s, m, n, haeq, hp, ho⟩ := hrule.orient_member hin
    have hres : residual = {(Term.ternary .penc k s n).baseClass} + rest := by
      have hh := hs'.symm.trans hs
      simpa only [haeq, hp, ciphertextPairFactors, Multiset.insert_eq_cons,
        Multiset.cons_add, Multiset.singleton_add, Multiset.cons_inj_right] using hh
    have hstep : ModuloStep (.ternary .penc k r m) b :=
      hab.pre_base ((baseClass_eq_iff _ _).mp haeq.symm)
    exact (selected_ciphertext_fusion_joined source u v k r s m n b rest hstep
      (by simpa only [hp] using hs) (by simpa only [ho] using hu)
      (by simpa only [hres] using hv)).2.2
  · obtain ⟨remaining, hremaining⟩ := Multiset.exists_cons_of_mem hout
    have hrest : rest = {a.baseClass} + remaining := by
      simpa only [Multiset.singleton_add] using hremaining
    obtain ⟨k, r, s, m, n, rfl, rfl⟩ := hrule
    have hres : residual = ciphertextPairFactors k r s m n + remaining := by
      have hh := hs'.symm.trans hs
      rw [hrest, ← Multiset.add_assoc, Multiset.add_comm (ciphertextPairFactors k r s m n),
        Multiset.add_assoc] at hh
      exact Multiset.add_right_inj.mp hh
    exact (disjoint_fusion_reduction_joined source u v k r s m n a b remaining hab
      (by simpa only [ha, hrest] using hs)
      (by simpa only [ha, hrest] using hu) (by
        rw [hv, hres]
        rw [← Multiset.add_assoc, Multiset.add_comm b.mulFactors, Multiset.add_assoc])).2.2

end ExplainableCrypto.Helios.Symbolic
