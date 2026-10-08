import ExplainableCrypto.Helios.Symbolic.AcceptedBallotReconstruction

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

private theorem singleton_normal_representative (t : Term V) (ht : Irreducible t)
    {q : BaseClass V} (hq : q ∈ ({t.baseClass} : Multiset (BaseClass V))) :
    ∃ a : Term V, a.baseClass = q ∧ Irreducible a :=
  ⟨t, (Multiset.mem_singleton.mp hq).symm, ht⟩

/-- Every nonnumeric addition atom of a normal term has a normal representative. -/
theorem Irreducible.add_atom_representative {t : Term V} (ht : Irreducible t)
    {q : BaseClass V} (hq : q ∈ t.addSummary.atoms) :
    ∃ a : Term V, a.baseClass = q ∧ Irreducible a := by
  induction t with
  | binary f a b ia ib =>
    cases f with
    | add =>
      rcases Multiset.mem_add.mp hq with hq | hq
      · exact ia (ht.context_hole (.binaryLeft .add .hole b)) hq
      · exact ib (ht.context_hole (.binaryRight .add a .hole)) hq
    | _ => exact singleton_normal_representative _ ht hq
  | const c =>
    cases c with
    | zero | one => simp [Term.addSummary, AddSummary.number] at hq
    | ok | bottom => exact singleton_normal_representative _ ht hq
  | _ => exact singleton_normal_representative _ ht hq

/-- Addition of irreducible inputs is irreducible modulo E0, including numeric collapses. -/
theorem Irreducible.add {a b : Term V} (ha : Irreducible a) (hb : Irreducible b) :
    Irreducible (.binary .add a b) := by
  apply irreducible_of_add_summaries
  intro x _ hx
  rcases Multiset.mem_add.mp hx with hx | hx
  · obtain ⟨t, ht, hi⟩ := ha.add_atom_representative hx
    exact hi.base ((baseClass_eq_iff _ _).mp ht)
  · obtain ⟨t, ht, hi⟩ := hb.add_atom_representative hx
    exact hi.base ((baseClass_eq_iff _ _).mp ht)

/-- An atom-free summary represents a present natural number; it cannot be empty. -/
theorem Term.numeric_of_no_add_atoms (t : Term V) (ht : t.addSummary.atoms = 0) :
    ∃ k, BaseEq t (addNumeral k) := by
  cases hn : t.addSummary.numeric with
  | none =>
    exact False.elim (t.addSummary_ne_empty (AddSummary.eq_of_fields ht hn))
  | some k =>
    refine ⟨k, (baseEq_iff_addSummary _ _).mpr ?_⟩
    rw [addNumeral_summary]
    exact AddSummary.eq_of_fields ht hn

/-- Full-E numeric addition inversion, with arbitrary reducible operands. -/
theorem EqE.add_numeral_iff (a b : Term V) (k : Nat) :
    EqE (.binary .add a b) (addNumeral k) ↔
      ∃ p q, p + q = k ∧ EqE a (addNumeral p) ∧ EqE b (addNumeral q) := by
  constructor
  · intro he
    obtain ⟨a', hpa, hna⟩ := exists_normal_form a
    obtain ⟨b', hpb, hnb⟩ := exists_normal_form b
    have hsum := (irreducible_eqE_iff_base (hna.add hnb) (addNumeral_irreducible k)).mp
      ((EqE.binary .add hpa.sound hpb.sound).symm.trans he)
    have hs := hsum.add_summary
    rw [Term.addSummary, addNumeral_summary] at hs
    have hatoms := congrArg AddSummary.atoms hs
    have hcard := congrArg Multiset.card hatoms
    simp only [AddSummary.combine, AddSummary.number, Multiset.card_add, Multiset.card_zero] at hcard
    have hab : a'.addSummary.atoms = 0 ∧ b'.addSummary.atoms = 0 :=
      ⟨Multiset.card_eq_zero.mp (by omega), Multiset.card_eq_zero.mp (by omega)⟩
    obtain ⟨p, hap⟩ := a'.numeric_of_no_add_atoms hab.1
    obtain ⟨q, hbq⟩ := b'.numeric_of_no_add_atoms hab.2
    have hcount := congrArg AddSummary.numeric hs
    rw [hap.add_summary, hbq.add_summary, addNumeral_summary, addNumeral_summary,
      AddSummary.combine_numbers] at hcount
    refine ⟨p, q, Option.some.inj hcount, hpa.sound.trans hap.sound, hpb.sound.trans hbq.sound⟩
  · rintro ⟨p, q, rfl, ha, hb⟩
    exact (EqE.binary .add ha hb).trans (addNumerals_combine p q).sound

theorem EqE.add_zero_iff (a b : Term V) :
    EqE (.binary .add a b) (.const .zero) ↔ EqE a (.const .zero) ∧ EqE b (.const .zero) := by
  constructor
  · intro h
    obtain ⟨p, q, hpq, ha, hb⟩ := (EqE.add_numeral_iff a b 0).mp h
    have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst p; subst q
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    exact (EqE.binary .add ha hb).trans (.equation .zero_zero)

theorem EqE.add_one_iff (a b : Term V) :
    EqE (.binary .add a b) (.const .one) ↔
      (EqE a (.const .zero) ∧ EqE b (.const .one)) ∨
      (EqE a (.const .one) ∧ EqE b (.const .zero)) := by
  constructor
  · intro h
    obtain ⟨p, q, hpq, ha, hb⟩ := (EqE.add_numeral_iff a b 1).mp
      (h.trans (EqE.equation .zero_one).symm)
    have hp : p = 0 ∨ p = 1 := by omega
    rcases hp with rfl | rfl
    · have hq : q = 1 := by omega
      subst q
      exact Or.inl ⟨ha, hb.trans (.equation .zero_one)⟩
    · have hq : q = 0 := by omega
      subst q
      exact Or.inr ⟨ha.trans (.equation .zero_one), hb⟩
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact (EqE.binary .add ha hb).trans (.equation .zero_one)
    · exact (EqE.binary .add ha hb).trans
        ((EqE.equation (.comm .add trivial _ _)).trans (.equation .zero_one))

/-- A term whose full E-value is one of the two vote bits. -/
def BitValue (t : Term V) : Prop := EqE t (.const .zero) ∨ EqE t (.const .one)

theorem BitValue.add_components {a b : Term V} (h : BitValue (.binary .add a b)) :
    BitValue a ∧ BitValue b := by
  rcases h with hz | ho
  · obtain ⟨ha, hb⟩ := (EqE.add_zero_iff _ _).mp hz
    exact ⟨Or.inl ha, Or.inl hb⟩
  · rcases (EqE.add_one_iff _ _).mp ho with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact ⟨Or.inl ha, Or.inr hb⟩
    · exact ⟨Or.inr ha, Or.inl hb⟩

end ExplainableCrypto.Helios.Symbolic
