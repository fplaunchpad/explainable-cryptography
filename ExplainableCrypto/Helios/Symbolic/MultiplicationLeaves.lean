import ExplainableCrypto.Helios.Symbolic.MultiplicationPartitions

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type}

/-- Raw outer-multiplication leaves, preserving duplicate occurrences. -/
def Term.mulLeaves : Term V → Multiset (Term V)
  | .binary .mul a b => a.mulLeaves + b.mulLeaves
  | t => {t}

/-- Every flattened leaf is a genuine syntactic subterm and is not a raw
multiplication node. Its value may still be reducible. -/
theorem Term.mulLeaves_mem {r a : Term V} (ha : a ∈ r.mulLeaves) :
    (∃ c : Context V, c.fill a = r) ∧ (∀ x y, a ≠ .binary .mul x y) := by
  induction r with
  | binary f x y ix iy =>
    cases f with
    | mul =>
      rcases Multiset.mem_add.mp ha with hx | hy
      · obtain ⟨⟨c, hc⟩, hn⟩ := ix hx
        exact ⟨⟨.binaryLeft .mul c y, by simp only [Context.fill, hc]⟩, hn⟩
      · obtain ⟨⟨c, hc⟩, hn⟩ := iy hy
        exact ⟨⟨.binaryRight .mul x c, by simp only [Context.fill, hc]⟩, hn⟩
    | pair | compose | add | partialDecrypt | dec =>
      have he : a = _ := Multiset.mem_singleton.mp ha
      subst a
      exact ⟨⟨.hole, rfl⟩, by intro _ _ h; cases h⟩
  | name | var | const | unary | ternary | spk =>
    have he : a = _ := Multiset.mem_singleton.mp ha
    subst a
    exact ⟨⟨.hole, rfl⟩, by intro _ _ h; cases h⟩


end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Every raw non-mul leaf of a minimum recipe has a single-factor normal
representative in both worlds. Ciphertext leaves remain allowed. -/
theorem minimum_mul_leaf_normal_forms (ns : Names n)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right) r.nodeCount) :
    (∀ a ∈ r.mulLeaves, ∃ t, ReducesModulo ((frame ns false left right).eval a) t ∧
      Irreducible t ∧ (∀ x y, t ≠ .binary .mul x y)) ∧
    (∀ a ∈ r.mulLeaves, ∃ t, ReducesModulo ((frame ns true left right).eval a) t ∧
      Irreducible t ∧ (∀ x y, t ≠ .binary .mul x y)) := by
  have info {a : Recipe 3} (ha : a ∈ r.mulLeaves) :
      MinimalRecipe ns.restricted (frame ns false left right).value a ∧
      a.nodeCount ≤ r.nodeCount ∧ (∀ x y, a ≠ .binary .mul x y) := by
    obtain ⟨⟨c, hc⟩, hn⟩ := Term.mulLeaves_mem ha
    have hmc := hm
    rw [← hc] at hmc
    exact ⟨hmc.subterm c, by simpa only [hc] using c.nodeCount_hole_le a, hn⟩
  constructor
  · intro a ha
    have hi := info ha
    obtain ⟨t, ht, hn⟩ := exists_normal_form ((frame ns false left right).eval a)
    refine ⟨t, ht.to_modulo, hn, ?_⟩
    intro x y he
    subst t
    obtain ⟨u, v, huv⟩ := minimum_normal_mul_form ns false left right ns.restricted a hi.1 hn ht.sound
    exact hi.2.2 u v huv
  · intro a ha
    have hi := info ha
    obtain ⟨t, ht, hn⟩ := exists_normal_form ((frame ns true left right).eval a)
    refine ⟨t, ht.to_modulo, hn, ?_⟩
    intro x y he
    subst t
    obtain ⟨u, v, huv⟩ := minimum_normal_mul_form_after_swap ns left right a hi.1 (hobs.mono hi.2.1) hn ht.sound
    exact hi.2.2 u v huv

end ExplainableCrypto.Helios.Symbolic.Historical.General
