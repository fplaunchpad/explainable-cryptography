import ExplainableCrypto.Helios.Symbolic.Separation

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- E3 and E7 turn the homomorphic combination into an encryption of one. -/
theorem combined_zero_one (k r s : Term V) : EqE
    (.binary .mul (.ternary .penc k r (.const .zero)) (.ternary .penc k s (.const .one)))
    (.ternary .penc k (.binary .compose r s) (.const .one)) :=
  (EqE.equation (.homomorphic k r s (.const .zero) (.const .one))).trans
    (.ternary .penc (.refl _) (.refl _) (.equation .zero_one))

/-- The source's Example 1, for plaintexts (zero, one), with its actual proof term. -/
theorem aggregate_example (k r s : Term V) :
    let c := Term.binary .mul (.ternary .penc k r (.const .zero))
      (.ternary .penc k s (.const .one))
    EqE (.ternary .checkspk k c
      (.spk k (.binary .compose r s) (.binary .add (.const .zero) (.const .one)) c))
      (.const .ok) := by
  dsimp
  have hc := combined_zero_one k r s
  exact (EqE.ternary .checkspk (.refl _) hc
    (.spk (.refl _) (.refl _) (.equation .zero_one) hc)).trans
      (.equation (.check_one k (.binary .compose r s)))

/-- Swapping both ciphertexts and their aggregate proof statement preserves its check. -/
theorem aggregate_permutation (k r s : Term V) :
    let a := Term.ternary .penc k r (.const .zero)
    let b := Term.ternary .penc k s (.const .one)
    let proof := Term.spk k (.binary .compose r s)
      (.binary .add (.const .zero) (.const .one)) (.binary .mul a b)
    EqE (.ternary .checkspk k (.binary .mul b a) proof) (.const .ok) := by
  dsimp
  exact (EqE.ternary .checkspk (.refl _) (.equation (.comm .mul trivial _ _))
    (.refl _)).trans (aggregate_example k r s)

/-- A public partial decryption exposes the associated plaintext, as required by E6. -/
theorem partial_decryption_observable (k r m : Term V) : EqE
    (.binary .dec (.binary .partialDecrypt k (.ternary .penc (.unary .pk k) r m))
      (.ternary .penc (.unary .pk k) r m)) m := .equation (.partial_decrypt k r m)

/-- Tally symmetry for arbitrary further contributions; no identity law is used. -/
theorem honest_tally_swap (a b : Term V) (rest : List (Term V)) : EqE
    (rest.foldl (.binary .add) (.binary .add a b))
    (rest.foldl (.binary .add) (.binary .add b a)) := by
  have lift : ∀ (xs : List (Term V)) (x y : Term V), EqE x y →
      EqE (xs.foldl (.binary .add) x) (xs.foldl (.binary .add) y) := by
    intro xs
    induction xs with
    | nil => intro x y h; exact h
    | cons c cs ih => intro x y h; exact ih _ _ (.binary .add h (.refl c))
  exact lift rest _ _ (.equation (.comm .add trivial a b))

theorem public_handle_allowed : (Term.var (0 : Fin 1)).Public {7} := trivial

theorem secret_name_forbidden : ¬ (Term.name (V := Fin 1) 7).Public {7} := by
  simp [Term.Public]

theorem public_name_allowed : (Term.name (V := Fin 1) 8).Public {7} := by
  simp [Term.Public]

/-- Public recipes may copy a handle; privacy must cope with copying. -/
theorem replay_recipe_allowed :
    (Term.binary .pair (.var (0 : Fin 1)) (.var 0)).Public {7} := ⟨trivial, trivial⟩

/-- Control: static equivalence can distinguish a published zero from a published one. -/
theorem published_bit_distinguishable :
    ¬ Frame.StaticEq (restricted := {7}) (n := 1)
      ⟨fun _ => .const .zero⟩ ⟨fun _ => .const .one⟩ := by
  intro h
  have bad := (h (.var 0) (.const .zero) trivial trivial).mp (.refl _)
  exact zero_not_one bad.symm

/-- Control: equationally equal but syntactically different outputs remain equivalent. -/
theorem reduced_bit_staticEq :
    Frame.StaticEq (restricted := {7}) (n := 1)
      ⟨fun _ => .binary .add (.const .zero) (.const .one)⟩ ⟨fun _ => .const .one⟩ :=
  Frame.staticEq_of_pointwise (fun _ => .equation .zero_one)

end ExplainableCrypto.Helios.Symbolic
