import ExplainableCrypto.Helios.Symbolic.BaseStructure
import ExplainableCrypto.Helios.Symbolic.Confluence

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Same-position root peaks modulo E0, excluding the homomorphic AC operator.
No local-confluence premise or raw-equality conclusion is used. -/
theorem rigid_root_outputs_base {a b a' b' : Term V}
    (ha : RootStep a b) (hb : RootStep a' b') (he : BaseEq a a')
    (hrigid : a.headTag ≠ .binary .mul) : BaseEq b b' := by
  cases ha <;> cases hb <;> first
    | exact .refl _
    | exact (by simpa [Term.rigidArgument] using (he.argument 0).argument 0)
    | exact (by simpa [Term.rigidArgument] using (he.argument 0).argument 1)
    | exact (by simpa [Term.rigidArgument] using (he.argument 1).argument 2)
    | exact False.elim (hrigid rfl)
    | exact False.elim (by have hh := he.head_eq; simp [Term.headTag] at hh)

/-- Both competing root steps are transported to the same source. -/
theorem rigid_root_peak_joined {a b a' b' : Term V}
    (ha : RootStep a b) (hb : RootStep a' b') (he : BaseEq a a')
    (hrigid : a.headTag ≠ .binary .mul) :
    ModuloStep a b ∧ ModuloStep a b' ∧ JoinModulo b b' :=
  ⟨ha.to_modulo, hb.to_modulo.pre_base he,
    ⟨b', .base (rigid_root_outputs_base ha hb he hrigid), .refl _⟩⟩

namespace RigidRootSPOT

/-- Projection outputs can differ in raw syntax even in a joined rigid root peak. -/
theorem projection_outputs_not_identical :
    let z : Term Nat := .const .zero
    let zz := Term.binary .add z z
    let a := Term.unary .fst (.binary .pair z (.const .one))
    let a' := Term.unary .fst (.binary .pair zz (.const .one))
    BaseEq a a' ∧ RootStep a z ∧ RootStep a' zz ∧
      JoinModulo z zz ∧ z ≠ zz := by
  dsimp
  have he : BaseEq (Term.unary .fst (.binary .pair (.const .zero) (.const .one)))
      (.unary .fst (.binary .pair (.binary .add (.const .zero) (.const .zero)) (.const .one)) : Term Nat) :=
    .unary .fst (.binary .pair (BaseEq.equation .zero_zero).symm (.refl _))
  exact ⟨he, .fst _ _, .fst _ _,
    (rigid_root_peak_joined (.fst _ _) (.fst _ _) he (by decide)).2.2, by decide⟩

/-- E0 can change a ciphertext nonce without changing the decryption result. -/
theorem decrypt_commuted_nonce :
    let a : Term Nat := .binary .dec (.name 0)
      (.ternary .penc (.unary .pk (.name 0)) (.binary .compose (.name 1) (.name 2)) (.const .one))
    let a' : Term Nat := .binary .dec (.name 0)
      (.ternary .penc (.unary .pk (.name 0)) (.binary .compose (.name 2) (.name 1)) (.const .one))
    BaseEq a a' ∧ RootStep a (.const .one) ∧ RootStep a' (.const .one) ∧
      JoinModulo (.const .one : Term Nat) (.const .one) := by
  dsimp
  have he : BaseEq (Term.binary .dec (.name 0)
      (.ternary .penc (.unary .pk (.name 0)) (.binary .compose (.name 1) (.name 2)) (.const .one)))
      (.binary .dec (.name 0)
      (.ternary .penc (.unary .pk (.name 0)) (.binary .compose (.name 2) (.name 1)) (.const .one)) : Term Nat) :=
    .binary .dec (.refl _) (.ternary .penc (.refl _)
      (.equation (.comm .compose trivial _ _)) (.refl _))
  exact ⟨he, .decrypt _ _ _, .decrypt _ _ _,
    (rigid_root_peak_joined (.decrypt _ _ _) (.decrypt _ _ _) he (by decide)).2.2⟩

end RigidRootSPOT
end ExplainableCrypto.Helios.Symbolic
