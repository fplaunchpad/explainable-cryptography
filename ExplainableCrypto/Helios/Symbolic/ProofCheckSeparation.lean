import ExplainableCrypto.Helios.Symbolic.ProofCheckPaths
import ExplainableCrypto.Helios.Symbolic.ProjectionPaths

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- A target with a stable head distinct from checkspk and ok cannot be a check value. -/
theorem proof_check_not_eqE_of_stable_head (a b c t : Term V)
    (hs : ∀ w, ReducesModulo t w → w.headTag = t.headTag)
    (hcheck : t.headTag ≠ (.ternary .checkspk a b c : Term V).headTag)
    (hok : t.headTag ≠ (.const .ok : Term V).headTag) :
    ¬ EqE (.ternary .checkspk a b c) t := by
  intro h
  obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp h
  have hh := hs w hr
  rcases hl.proof_check_shape with ⟨a', b', c', rfl⟩ | rfl
  · exact hcheck hh.symm
  · exact hok hh.symm

theorem proof_check_not_eqE_penc (a b c k r m : Term V) :
    ¬ EqE (.ternary .checkspk a b c) (.ternary .penc k r m) := by
  apply proof_check_not_eqE_of_stable_head a b c _
  · intro w hw
    obtain ⟨_, _, _, he, _⟩ := hw.penc_components
    exact he.head_eq
  · simp [Term.headTag]
  · simp [Term.headTag]

theorem proof_check_not_eqE_passive_binary (f : Binary) (hf : f = .pair ∨ f = .partialDecrypt)
    (a b c x y : Term V) : ¬ EqE (.ternary .checkspk a b c) (.binary f x y) := by
  apply proof_check_not_eqE_of_stable_head a b c _
  · intro w hw
    obtain ⟨_, _, he, _⟩ := hw.passive_binary_components hf
    rcases hf with rfl | rfl <;> exact he.head_eq
  · rcases hf with rfl | rfl <;> simp [Term.headTag]
  · rcases hf with rfl | rfl <;> simp [Term.headTag]

theorem proof_check_not_eqE_spk (a b c k r m d : Term V) :
    ¬ EqE (.ternary .checkspk a b c) (.spk k r m d) := by
  apply proof_check_not_eqE_of_stable_head a b c _
  · intro w hw
    obtain ⟨_, _, _, _, he, _⟩ := hw.spk_components
    exact he.head_eq
  · simp [Term.headTag]
  · simp [Term.headTag]

theorem proof_check_not_eqE_pk (a b c k : Term V) :
    ¬ EqE (.ternary .checkspk a b c) (.unary .pk k) := by
  apply proof_check_not_eqE_of_stable_head a b c _
  · intro w hw
    obtain ⟨_, he, _⟩ := hw.pk_components
    exact he.head_eq
  · simp [Term.headTag]
  · simp [Term.headTag]

theorem proof_check_not_eqE_name (a b c : Term V) (n : Nat) :
    ¬ EqE (.ternary .checkspk a b c) (.name n) := by
  apply proof_check_not_eqE_of_stable_head a b c _
  · exact fun _ hw => ((name_irreducible n).reducesModulo hw).head_eq.symm
  · simp [Term.headTag]
  · simp [Term.headTag]

theorem proof_check_not_eqE_var (a b c : Term V) (v : V) :
    ¬ EqE (.ternary .checkspk a b c) (.var v) := by
  apply proof_check_not_eqE_of_stable_head a b c _
  · exact fun _ hw => ((var_irreducible v).reducesModulo hw).head_eq.symm
  · simp [Term.headTag]
  · simp [Term.headTag]

theorem EqE.proof_check_constant_cases {a b c : Term V} {d : Constant}
    (h : EqE (.ternary .checkspk a b c) (.const d)) : d = .ok := by
  rcases h.proof_check_irreducible_shape (constant_irreducible d) with
    ⟨_, _, _, he, _⟩ | ⟨_, he⟩
  · cases he
  · exact Term.const.inj he

end ExplainableCrypto.Helios.Symbolic
