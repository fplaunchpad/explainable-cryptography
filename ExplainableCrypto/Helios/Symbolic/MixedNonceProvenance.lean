import ExplainableCrypto.Helios.Symbolic.CiphertextCombinations

namespace ExplainableCrypto.Helios.Symbolic
variable {V α : Type} {restricted : Finset Nat}

/-- A public value may be represented by a raw-unsafe term. Protection is
required only of some E-equal value, which can then be normalized internally. -/
def ProtectedValue (restricted : Finset Nat) (r : Term V) : Prop :=
  ∃ r', EqE r r' ∧ r'.nonceSafe restricted = true

theorem ProtectedValue.of_safe {r : Term V} (h : r.nonceSafe restricted = true) :
    ProtectedValue restricted r := ⟨r, .refl _, h⟩

theorem ProtectedValue.normal_rep {r : Term V} (h : ProtectedValue restricted r) :
    ∃ r', EqE r r' ∧ Irreducible r' ∧ r'.nonceSafe restricted = true := by
  obtain ⟨r₀, he, hs⟩ := h
  obtain ⟨r', hp, hn⟩ := exists_normal_form r₀
  have hs' : r'.nonceSafe restricted = true := by
    clear hn
    induction hp with
    | refl => exact hs
    | tail _ step ih => exact step.nonce_safe ih
  exact ⟨r', he.trans hp.sound, hn, hs'⟩

theorem Irreducible.compose_factor_representative {t : Term V} (ht : Irreducible t)
    {q : BaseClass V} (hq : q ∈ t.composeFactors) :
    ∃ a : Term V, a.baseClass = q ∧ Irreducible a := by
  induction t with
  | binary f a b ia ib =>
    cases f with
    | compose =>
      rcases Multiset.mem_add.mp hq with hq | hq
      · exact ia (ht.context_hole (.binaryLeft .compose .hole b)) hq
      · exact ib (ht.context_hole (.binaryRight .compose a .hole)) hq
    | _ => exact ⟨_, (Multiset.mem_singleton.mp hq).symm, ht⟩
  | _ => exact ⟨_, (Multiset.mem_singleton.mp hq).symm, ht⟩

theorem Irreducible.compose {a b : Term V} (ha : Irreducible a) (hb : Irreducible b) :
    Irreducible (.binary .compose a b) := by
  apply irreducible_of_compose_factors
  intro x _ hx
  rcases Multiset.mem_add.mp hx with hx | hx
  · obtain ⟨t, ht, hi⟩ := ha.compose_factor_representative hx
    exact hi.base ((baseClass_eq_iff _ _).mp ht)
  · obtain ⟨t, ht, hi⟩ := hb.compose_factor_representative hx
    exact hi.base ((baseClass_eq_iff _ _).mp ht)

/-- A predicate separates two multiset components without forgetting multiplicity. -/
theorem separated_multiset_add_eq_iff (p : α → Prop) (r s a b : Multiset α)
    (hr : ∀ x ∈ r, ¬ p x) (hs : ∀ x ∈ s, ¬ p x)
    (ha : ∀ x ∈ a, p x) (hb : ∀ x ∈ b, p x) :
    r + a = s + b ↔ r = s ∧ a = b := by
  classical
  constructor
  · intro he
    have hf := congrArg (Multiset.filter p) he
    rw [Multiset.filter_add, Multiset.filter_add,
      Multiset.filter_eq_nil.mpr hr, Multiset.filter_eq_nil.mpr hs,
      Multiset.filter_eq_self.mpr ha, Multiset.filter_eq_self.mpr hb] at hf
    have hab : a = b := by simpa using hf
    exact ⟨add_right_cancel (hab ▸ he), hab⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Normal representatives with no protected outer name factors separate the
public remainder from every honest occurrence. This structural statement is
independent of how a caller establishes factor protection. -/
theorem mixed_named_nonce_eq_iff_of_normal_factors (names : α → Nat) (hf : Function.Injective names)
    (a b : Combination α) (r s : Term V)
    (hr : ∃ r', EqE r r' ∧ Irreducible r' ∧ ∀ i, (Term.name (V := V) (names i)).baseClass ∉ r'.composeFactors)
    (hs : ∃ s', EqE s s' ∧ Irreducible s' ∧ ∀ i, (Term.name (V := V) (names i)).baseClass ∉ s'.composeFactors) :
    EqE (.binary .compose r (a.evaluate .compose (fun i => .name (names i))))
      (.binary .compose s (b.evaluate .compose (fun i => .name (names i)))) ↔
      a.indices = b.indices ∧ EqE r s := by
  constructor
  · intro he
    obtain ⟨r', her, hnr, hsr⟩ := hr
    obtain ⟨s', hes, hns, hss⟩ := hs
    have he' := (EqE.binary .compose her (.refl _)).symm.trans
      (he.trans (EqE.binary .compose hes (.refl _)))
    have hb := (irreducible_eqE_iff_base
      (hnr.compose (Combination.named_nonce_irreducible names a))
      (hns.compose (Combination.named_nonce_irreducible names b))).mp he'
    have hbag := hb.compose_factors
    simp only [Term.composeFactors, Combination.named_nonce_factors] at hbag
    let p := fun q : BaseClass V => ∃ i, q = (Term.name (V := V) (names i)).baseClass
    have hR : ∀ q ∈ r'.composeFactors, ¬ p q := by
      rintro q hq ⟨i, rfl⟩
      exact hsr i hq
    have hS : ∀ q ∈ s'.composeFactors, ¬ p q := by
      rintro q hq ⟨i, rfl⟩
      exact hss i hq
    have hA (t : Combination α) : ∀ q ∈ t.indices.map (fun i => (Term.name (V := V) (names i)).baseClass), p q := by
      intro q hq
      obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hq
      exact ⟨i, rfl⟩
    obtain ⟨hrem, hindices⟩ := (separated_multiset_add_eq_iff p _ _ _ _ hR hS (hA a) (hA b)).mp hbag
    have hi : a.indices = b.indices := by
      apply Multiset.map_injective (f := fun i => (Term.name (V := V) (names i)).baseClass) ?_ hindices
      intro i j hij
      exact hf ((BaseEq.name_iff _ _).mp ((baseClass_eq_iff _ _).mp hij))
    exact ⟨hi, her.trans (((baseEq_iff_composeFactors _ _).mpr hrem).sound.trans hes.symm)⟩
  · rintro ⟨hi, he⟩
    exact EqE.binary .compose he
      (Combination.evaluate_baseEq_of_indices .compose trivial (fun i => .name (names i)) hi).sound

/-- Protected remainders cannot compensate for a changed honest nonce bag.
Both remainders may be reducible and need not be raw-syntactically protected. -/
theorem mixed_named_nonce_eq_iff (names : α → Nat) (hf : Function.Injective names)
    (hnames : ∀ i, names i ∈ restricted) (a b : Combination α) (r s : Term V)
    (hr : ProtectedValue restricted r) (hs : ProtectedValue restricted s) :
    EqE (.binary .compose r (a.evaluate .compose (fun i => .name (names i))))
      (.binary .compose s (b.evaluate .compose (fun i => .name (names i)))) ↔
      a.indices = b.indices ∧ EqE r s := by
  apply mixed_named_nonce_eq_iff_of_normal_factors names hf a b r s
  · obtain ⟨r',he,hn,hs⟩ := hr.normal_rep
    exact ⟨r',he,hn,fun i => r'.nonce_safe_no_name_factor hs (hnames i)⟩
  · obtain ⟨s',he,hn,hs⟩ := hs.normal_rep
    exact ⟨s',he,hn,fun i => s'.nonce_safe_no_name_factor hs (hnames i)⟩

end ExplainableCrypto.Helios.Symbolic
