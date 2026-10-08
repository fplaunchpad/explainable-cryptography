import ExplainableCrypto.Helios.Symbolic.AdditionHeads
import ExplainableCrypto.Helios.Symbolic.CompositionHeads
import ExplainableCrypto.Helios.Symbolic.MultiplicationHeads

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- The E0 head tag groups add/zero/one; compose retains its own tag. -/
theorem ReducesModulo.arithmetic_head_tag {f : Binary} (hf : f = .add ∨ f = .compose)
    {a b t : Term V} (h : ReducesModulo (.binary f a b) t) :
    t.headTag = (Term.binary f a b).headTag := by
  rcases hf with rfl | rfl
  · rcases h.add_shape with ⟨x, y, rfl⟩ | rfl | rfl <;> rfl
  · obtain ⟨x, y, rfl⟩ := h.compose_shape
    rfl

theorem EqE.arithmetic_irreducible_head_tag {f : Binary} (hf : f = .add ∨ f = .compose)
    {a b t : Term V} (h : EqE (.binary f a b) t) (ht : Irreducible t) :
    t.headTag = (Term.binary f a b).headTag := by
  obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp h
  exact (ht.reducesModulo hr).head_eq.trans (hl.arithmetic_head_tag hf)

/-- A reusable exclusion criterion with an explicit stable-target-head premise. -/
theorem arithmetic_not_eqE_of_stable_head (f : Binary) (hf : f = .add ∨ f = .compose)
    (a b t : Term V) (hs : ∀ w, ReducesModulo t w → w.headTag = t.headTag)
    (hne : (Term.binary f a b).headTag ≠ t.headTag) : ¬ EqE (.binary f a b) t := by
  intro h
  obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp h
  exact hne ((hl.arithmetic_head_tag hf).symm.trans (hs w hr))

theorem arithmetic_not_eqE_penc (f : Binary) (hf : f = .add ∨ f = .compose)
    (a b key nonce message : Term V) :
    ¬ EqE (.binary f a b) (.ternary .penc key nonce message) := by
  apply arithmetic_not_eqE_of_stable_head f hf a b _
  · intro w hw
    obtain ⟨_, _, _, he, _⟩ := hw.penc_components
    exact he.head_eq
  · rcases hf with rfl | rfl <;> simp [Term.headTag]

theorem arithmetic_not_eqE_passive_binary (f g : Binary) (hf : f = .add ∨ f = .compose)
    (hg : g = .pair ∨ g = .partialDecrypt) (a b x y : Term V) :
    ¬ EqE (.binary f a b) (.binary g x y) := by
  apply arithmetic_not_eqE_of_stable_head f hf a b _
  · intro w hw
    obtain ⟨_, _, he, _⟩ := hw.passive_binary_components hg
    rcases hg with rfl | rfl <;> exact he.head_eq
  · rcases hf with rfl | rfl <;> rcases hg with rfl | rfl <;> simp [Term.headTag]

theorem arithmetic_not_eqE_spk (f : Binary) (hf : f = .add ∨ f = .compose)
    (a b k r m c : Term V) : ¬ EqE (.binary f a b) (.spk k r m c) := by
  apply arithmetic_not_eqE_of_stable_head f hf a b _
  · intro w hw
    obtain ⟨_, _, _, _, he, _⟩ := hw.spk_components
    exact he.head_eq
  · rcases hf with rfl | rfl <;> simp [Term.headTag]

theorem arithmetic_not_eqE_pk (f : Binary) (hf : f = .add ∨ f = .compose)
    (a b k : Term V) : ¬ EqE (.binary f a b) (.unary .pk k) := by
  apply arithmetic_not_eqE_of_stable_head f hf a b _
  · intro w hw
    obtain ⟨_, he, _⟩ := hw.pk_components
    exact he.head_eq
  · rcases hf with rfl | rfl <;> simp [Term.headTag]

theorem arithmetic_not_eqE_name (f : Binary) (hf : f = .add ∨ f = .compose)
    (a b : Term V) (n : Nat) : ¬ EqE (.binary f a b) (.name n) := by
  apply arithmetic_not_eqE_of_stable_head f hf a b _
  · intro w hw
    exact ((name_irreducible n).reducesModulo hw).head_eq.symm
  · rcases hf with rfl | rfl <;> simp [Term.headTag]

theorem arithmetic_not_eqE_var (f : Binary) (hf : f = .add ∨ f = .compose)
    (a b : Term V) (v : V) : ¬ EqE (.binary f a b) (.var v) := by
  apply arithmetic_not_eqE_of_stable_head f hf a b _
  · intro w hw
    exact ((var_irreducible v).reducesModulo hw).head_eq.symm
  · rcases hf with rfl | rfl <;> simp [Term.headTag]

/-- Only addition's zero/one numeric class is compatible with a constant result. -/
theorem EqE.arithmetic_constant_cases {f : Binary} (hf : f = .add ∨ f = .compose)
    {a b : Term V} {c : Constant} (h : EqE (.binary f a b) (.const c)) :
    f = .add ∧ (c = .zero ∨ c = .one) := by
  have hh := h.arithmetic_irreducible_head_tag hf (constant_irreducible c)
  rcases hf with rfl | rfl <;> cases c <;> simp_all [Term.headTag]

theorem compose_not_eqE_add (a b x y : Term V) :
    ¬ EqE (.binary .compose a b) (.binary .add x y) := by
  apply arithmetic_not_eqE_of_stable_head .compose (Or.inr rfl) a b _
  · exact fun _ h => h.arithmetic_head_tag (Or.inl rfl)
  · simp [Term.headTag]

theorem arithmetic_not_eqE_mul (f : Binary) (hf : f = .add ∨ f = .compose)
    (a b x y : Term V) : ¬ EqE (.binary f a b) (.binary .mul x y) := by
  intro h
  obtain ⟨t, ht, hi⟩ := exists_normal_form (Term.binary .mul x y)
  have hh := (h.trans ht.sound).arithmetic_irreducible_head_tag hf hi
  rcases ht.sound.mul_irreducible_shape hi with ⟨u, v, rfl⟩ | ⟨k, r, m, rfl⟩ <;>
    rcases hf with rfl | rfl <;> cases hh

end ExplainableCrypto.Helios.Symbolic
