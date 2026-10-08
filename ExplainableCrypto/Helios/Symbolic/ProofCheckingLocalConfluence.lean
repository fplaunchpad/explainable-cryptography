import ExplainableCrypto.Helios.Symbolic.ProofCheckingOverlap

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- E8/E9 exhaust checking roots, including their bit guard and bound ciphertext. -/
theorem RootModuloStep.proof_check_cases {a b c t : Term V}
    (h : RootModuloStep (.ternary .checkspk a b c) t) :
    ∃ k r bit, (bit = Constant.zero ∨ bit = .one) ∧ BaseEq a k ∧
      BaseEq b (bitCiphertext k r bit) ∧ BaseEq c (bitProof k r bit) ∧ BaseEq (.const .ok) t := by
  obtain ⟨l, r, he, hr, ht⟩ := h
  cases hr with
  | check_zero =>
    obtain ⟨_, ha, hb, hc⟩ := (BaseEq.ternary_iff _ _ _ _ _ _ _ _).mp he
    exact ⟨_, _, .zero, Or.inl rfl, ha, hb, hc, ht⟩
  | check_one =>
    obtain ⟨_, ha, hb, hc⟩ := (BaseEq.ternary_iff _ _ _ _ _ _ _ _).mp he
    exact ⟨_, _, .one, Or.inr rfl, ha, hb, hc, ht⟩
  | _ => have hh := he.head_eq; cases hh

/-- Any root check joins any argument step, with independent E0 representatives.
The common result is ok; no local-confluence hypothesis supplies this witness. -/
theorem proof_check_root_inner_joined {a b c u v : Term V}
    (hroot : RootModuloStep (.ternary .checkspk a b c) u)
    (hinner : TernaryArgumentStep .checkspk a b c v) : JoinModulo u v := by
  obtain ⟨k, r, bit, hb, ha, hc, hp, hout⟩ := hroot.proof_check_cases
  refine ⟨.const .ok, .base hout.symm, ?_⟩
  rcases hinner with ⟨a', hs, he⟩ | ⟨b', hs, he⟩ | ⟨c', hs, he⟩
  · exact (check_key_step_reduces k r bit hb (hs.pre_base ha.symm)).pre_base
      (he.trans (.ternary .checkspk (.refl _) hc hp))
  · exact (check_ballot_step_reduces k r bit hb (hs.pre_base hc.symm)).pre_base
      (he.trans (.ternary .checkspk ha (.refl _) hp))
  · exact (check_proof_step_reduces k r bit hb (hs.pre_base hp.symm)).pre_base
      (he.trans (.ternary .checkspk ha hc (.refl _)))

/-- All checking root/internal obligations are discharged. The three component
local-confluence hypotheses remain for competing argument reductions. -/
theorem locally_confluent_at_checkspk (a b c : Term V)
    (ha : LocallyConfluentAt a) (hb : LocallyConfluentAt b) (hc : LocallyConfluentAt c) :
    LocallyConfluentAt (.ternary .checkspk a b c) :=
  locally_confluent_at_ternary .checkspk a b c ha hb hc
    (fun _ _ hroot hinner => proof_check_root_inner_joined hroot hinner)

/-- At a root-matching check, every competing endpoint reduces to the fixed ok
result. Its irreducibility rules out an unrelated join witness. -/
theorem proof_check_step_reaches_ok {a b c t : Term V}
    (hr : RootModuloStep (.ternary .checkspk a b c) (.const .ok))
    (hs : ModuloStep (.ternary .checkspk a b c) t) : ReducesModulo t (.const .ok) := by
  rcases hs.ternary_cases with hs | hs
  · exact .base (hr.outputs_base hs).symm
  · obtain ⟨w, hok, htw⟩ := proof_check_root_inner_joined hr hs
    exact htw.post_base ((constant_irreducible .ok).reducesModulo hok).symm

/-- Matching checking sources have unconditional local confluence. The actual
root witness is essential and is not asserted for arbitrary checking terms. -/
theorem locally_confluent_at_matching_check {a b c : Term V}
    (hr : RootModuloStep (.ternary .checkspk a b c) (.const .ok)) :
    LocallyConfluentAt (.ternary .checkspk a b c) :=
  fun _ _ hu hv => ⟨.const .ok, proof_check_step_reaches_ok hr hu, proof_check_step_reaches_ok hr hv⟩

end ExplainableCrypto.Helios.Symbolic
