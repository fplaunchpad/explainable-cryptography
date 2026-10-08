import ExplainableCrypto.Helios.Symbolic.MinimumAdditionOrigins
import ExplainableCrypto.Helios.Symbolic.CompositionLeaves

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type}

/-- A raw addition skeleton keeps literal numeric summands separate from its
other recipe leaves. Occurrences, including duplicates, remain in the multiset. -/
def Term.addSyntaxSummary : Term V → AddSummary (Term V)
  | .const .zero => .number 0
  | .const .one => .number 1
  | .binary .add a b => a.addSyntaxSummary.combine b.addSyntaxSummary
  | t => .atom t

/-- Every nonnumeric leaf is a subterm with neither raw addition nor bit syntax. -/
theorem Term.addSyntaxSummary_mem {r a : Term V} (ha : a ∈ r.addSyntaxSummary.atoms) :
    (∃ c : Context V, c.fill a = r) ∧
    (∀ x y, a ≠ .binary .add x y) ∧ a ≠ .const .zero ∧ a ≠ .const .one := by
  induction r with
  | binary f x y ix iy =>
    cases f with
    | add =>
      rcases Multiset.mem_add.mp ha with hx | hy
      · obtain ⟨⟨c, hc⟩, hn⟩ := ix hx
        exact ⟨⟨.binaryLeft .add c y, by simp only [Context.fill, hc]⟩, hn⟩
      · obtain ⟨⟨c, hc⟩, hn⟩ := iy hy
        exact ⟨⟨.binaryRight .add x c, by simp only [Context.fill, hc]⟩, hn⟩
    | pair | mul | compose | partialDecrypt | dec =>
      have he : a = _ := Multiset.mem_singleton.mp ha
      subst a
      exact ⟨⟨.hole, rfl⟩, (by intro _ _ h; cases h), (by intro h; cases h), (by intro h; cases h)⟩
  | const c =>
    cases c with
    | zero | one => exact False.elim (Multiset.notMem_zero a ha)
    | ok | bottom =>
      have he : a = _ := Multiset.mem_singleton.mp ha
      subst a
      exact ⟨⟨.hole, rfl⟩, (by intro _ _ h; cases h), (by intro h; cases h), (by intro h; cases h)⟩
  | name | var | unary | ternary | spk =>
    have he : a = _ := Multiset.mem_singleton.mp ha
    subst a
    exact ⟨⟨.hole, rfl⟩, (by intro _ _ h; cases h), (by intro h; cases h), (by intro h; cases h)⟩

theorem Term.add_leaf_smaller {r leaf : Term V}
    (hr : (∃ a b, r = .binary .add a b) ∨ r = .const .zero ∨ r = .const .one)
    (h : leaf ∈ r.addSyntaxSummary.atoms) : leaf.nodeCount < r.nodeCount := by
  rcases hr with ⟨a, b, rfl⟩ | rfl | rfl
  · rcases Multiset.mem_add.mp h with ha | hb
    · obtain ⟨⟨c, hc⟩, _⟩ := Term.addSyntaxSummary_mem ha
      have hle := c.nodeCount_hole_le leaf
      rw [hc] at hle
      simp only [Term.nodeCount]
      omega
    · obtain ⟨⟨c, hc⟩, _⟩ := Term.addSyntaxSummary_mem hb
      have hle := c.nodeCount_hole_le leaf
      rw [hc] at hle
      simp only [Term.nodeCount]
      omega
  · exact False.elim (Multiset.notMem_zero leaf h)
  · exact False.elim (Multiset.notMem_zero leaf h)

/-- A semantic atom contributes one class and satisfies the path-stability premise. -/
theorem Term.add_value_atom {t : Term V} (h : t.fullClass.AddAtom) :
    t.addValueSummary = .atom t.fullClass ∧ t.AtomicAddFactors := by
  have he := Term.addValueSummary_atom (t := t)
    (by intro a b ht; subst t; exact h.1 a b rfl)
    (by intro ht; subst t; exact h.2.1 rfl)
    (by intro ht; subst t; exact h.2.2 rfl)
  refine ⟨he, ?_⟩
  intro q hq
  rw [he] at hq
  exact (Multiset.mem_singleton.mp hq) ▸ h

private theorem singleton_substitution (σ : V → Term W) (r : Term V)
    (hr : r.addSyntaxSummary = .atom r)
    (h : ∀ a ∈ r.addSyntaxSummary.atoms, (a.subst σ).fullClass.AddAtom) :
    (r.subst σ).addValueSummary =
      ⟨r.addSyntaxSummary.atoms.map (fun a => (a.subst σ).fullClass), r.addSyntaxSummary.numeric⟩ ∧
    (r.subst σ).AtomicAddFactors := by
  have he := Term.add_value_atom (h r (by rw [hr]; simp [AddSummary.atom]))
  simpa only [hr, AddSummary.atom, Multiset.map_singleton] using he

/-- Semantic atom conditions give exact substitution accounting, including the
unchanged optional numeric contribution and the path-stability premise. -/
theorem Term.add_leaves_substitution (σ : V → Term W) (r : Term V)
    (h : ∀ a ∈ r.addSyntaxSummary.atoms, (a.subst σ).fullClass.AddAtom) :
    (r.subst σ).addValueSummary =
      ⟨r.addSyntaxSummary.atoms.map (fun a => (a.subst σ).fullClass), r.addSyntaxSummary.numeric⟩ ∧
    (r.subst σ).AtomicAddFactors := by
  induction r with
  | binary f a b ia ib =>
    cases f with
    | add =>
      have ha := ia (fun x hx => h x (Multiset.mem_add.mpr (Or.inl hx)))
      have hb := ib (fun x hx => h x (Multiset.mem_add.mpr (Or.inr hx)))
      refine ⟨?_, ?_⟩
      · simp only [Term.subst, Term.addValueSummary, Term.addSyntaxSummary,
          ha.1, hb.1, AddSummary.combine, Multiset.map_add]
      · intro q hq
        rcases Multiset.mem_add.mp hq with hqa | hqb
        · exact ha.2 q hqa
        · exact hb.2 q hqb
    | pair | mul | compose | partialDecrypt | dec => exact singleton_substitution σ _ rfl h
  | const c =>
    cases c with
    | zero | one => exact ⟨rfl, by intro q hq; exact False.elim (Multiset.notMem_zero q hq)⟩
    | ok | bottom => exact singleton_substitution σ _ rfl h
  | _ => exact singleton_substitution σ _ rfl h

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Exact minimum origins make each nonnumeric raw leaf a semantic addition atom
in both worlds. Numeric constants are excluded because they also have add values. -/
theorem minimum_add_leaf_values (ns : Names n)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right) r.nodeCount) :
    (∀ a ∈ r.addSyntaxSummary.atoms, ((frame ns false left right).eval a).fullClass.AddAtom) ∧
    (∀ a ∈ r.addSyntaxSummary.atoms, ((frame ns true left right).eval a).fullClass.AddAtom) := by
  have info {a : Recipe 3} (ha : a ∈ r.addSyntaxSummary.atoms) :
      MinimalRecipe ns.restricted (frame ns false left right).value a ∧ a.nodeCount ≤ r.nodeCount ∧
      ¬ ((∃ x y, a = .binary .add x y) ∨ a = .const .zero ∨ a = .const .one) := by
    obtain ⟨⟨c, hc⟩, hn, hz, ho⟩ := Term.addSyntaxSummary_mem ha
    have hmc := hm
    rw [← hc] at hmc
    refine ⟨hmc.subterm c, by simpa only [hc] using c.nodeCount_hole_le a, ?_⟩
    rintro (⟨x, y, he⟩ | he | he)
    · exact hn x y he
    · exact hz he
    · exact ho he
  have atom_of_no_add {t : Ground} (h : ∀ x y, ¬ EqE t (.binary .add x y)) : t.fullClass.AddAtom := by
    refine ⟨fun x y he => h x y ((fullClass_eq_iff _ _).mp he), ?_, ?_⟩
    · intro he
      exact h _ _ (((fullClass_eq_iff _ _).mp he).trans (EqE.equation .zero_zero).symm)
    · intro he
      exact h _ _ (((fullClass_eq_iff _ _).mp he).trans (EqE.equation .zero_one).symm)
  constructor
  · intro a ha
    have hi := info ha
    exact atom_of_no_add (fun x y he => hi.2.2 (minimum_add_form ns false left right ns.restricted a hi.1 he))
  · intro a ha
    have hi := info ha
    exact atom_of_no_add (fun x y he => hi.2.2 (minimum_add_form_after_swap ns left right a hi.1 (hobs.mono hi.2.1) he))

end ExplainableCrypto.Helios.Symbolic.Historical.General
