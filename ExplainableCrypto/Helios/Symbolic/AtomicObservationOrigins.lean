import ExplainableCrypto.Helios.Symbolic.PairObservationInduction

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- All four constants remain distinct in full E, including zero versus one. -/
theorem EqE.const_iff (c d : Constant) : EqE (Term.const (V := V) c) (.const d) ↔ c = d := by
  constructor
  · intro he
    have hh := ((irreducible_eqE_iff_base (constant_irreducible c) (constant_irreducible d)).mp he).head_eq
    cases c <;> cases d <;> try rfl
    all_goals first
      | exact False.elim (zero_not_one he)
      | exact False.elim (zero_not_one he.symm)
      | cases hh
  · rintro rfl
    exact .refl _

theorem name_not_eqE_const (name : Nat) (c : Constant) :
    ¬ EqE (Term.name (V := V) name) (.const c) := by
  intro he
  have hh := ((irreducible_eqE_iff_base (name_irreducible name) (constant_irreducible c)).mp he).head_eq
  cases c <;> cases hh

/-- A ground term has no variable case, so node count one is exactly atomicity. -/
theorem ground_atom_cases {t : Ground} (ht : t.nodeCount = 1) :
    (∃ name, t = .name name) ∨ ∃ c, t = .const c := by
  rcases Term.nodeCount_one_cases (by omega : t.nodeCount ≤ 1) with
    ⟨name, rfl⟩ | ⟨v, _⟩ | ⟨c, rfl⟩
  · exact Or.inl ⟨name, rfl⟩
  · exact v.elim
  · exact Or.inr ⟨c, rfl⟩

theorem ground_atom_irreducible {t : Ground} (ht : t.nodeCount = 1) : Irreducible t := by
  rcases ground_atom_cases ht with ⟨name, rfl⟩ | ⟨c, rfl⟩
  · exact name_irreducible name
  · exact constant_irreducible c

/-- Equality of ground atoms is precisely literal equality, without merging
name/constant kinds or distinct constant symbols. -/
theorem EqE.ground_atoms_iff (a b : Ground) (ha : a.nodeCount = 1) (hb : b.nodeCount = 1) :
    EqE a b ↔ a = b := by
  rcases ground_atom_cases ha with ⟨x, rfl⟩ | ⟨c, rfl⟩
  · rcases ground_atom_cases hb with ⟨y, rfl⟩ | ⟨d, rfl⟩
    · simpa only [Term.name.injEq] using EqE.name_iff (V := Empty) x y
    · exact iff_of_false (name_not_eqE_const x d) (by intro h; cases h)
  · rcases ground_atom_cases hb with ⟨y, rfl⟩ | ⟨d, rfl⟩
    · exact iff_of_false (fun he => name_not_eqE_const y c he.symm) (by intro h; cases h)
    · simpa only [Term.const.injEq] using EqE.const_iff (V := Empty) c d

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Initial handles publish a public key or a nonempty ballot tuple, never an
atomic value. Arbitrary reducible candidate representatives are permitted. -/
theorem frame_handle_not_atom (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (v : Fin 3) (t : Ground) (ht : t.nodeCount = 1) :
    ¬ EqE ((frame ns swap left right).value v) t := by
  have hshape : (∃ k, EqE ((frame ns swap left right).value v) (.unary .pk k)) ∨
      ∃ a b, EqE ((frame ns swap left right).value v) (.binary .pair a b) := by
    fin_cases v
    · exact Or.inl ⟨_, .refl _⟩
    · exact Or.inr (ballot_tail_pair_value ns swap left right 0 0 (by unfold fieldCount; omega))
    · exact Or.inr (ballot_tail_pair_value ns swap left right 1 0 (by unfold fieldCount; omega))
  intro he
  rcases hshape with ⟨k, hk⟩ | ⟨a, b, hp⟩
  · obtain ⟨x, hx, _⟩ := (hk.symm.trans he).pk_irreducible_shape (ground_atom_irreducible ht)
    have hsize := congrArg Term.nodeCount hx
    have := x.nodeCount_pos
    simp only [Term.nodeCount] at hsize
    omega
  · obtain ⟨x, y, hx, _⟩ := (hp.symm.trans he).passive_binary_irreducible_shape
      (Or.inl rfl) (ground_atom_irreducible ht)
    have hsize := congrArg Term.nodeCount hx
    have := x.nodeCount_pos
    have := y.nodeCount_pos
    simp only [Term.nodeCount] at hsize
    omega

/-- Exact initial-frame name deducibility under the caller's policy. The
positive witness is the public literal; the negative direction covers all recipes. -/
theorem frame_name_deducible_iff (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (name : Nat) :
    (∃ r : Recipe 3, r.Public restricted ∧ EqE ((frame ns swap left right).eval r) (.name name)) ↔
      name ∉ restricted := by
  constructor
  · rintro ⟨r, hr, he⟩ hn
    exact frame_nonce_not_deducible ns swap left right r hr hn he
  · intro hn
    exact ⟨.name name, hn, .refl _⟩

/-- A deducible name is outside the caller's restricted set. Its literal public
recipe is therefore a size-one competitor, forcing exact minimum syntax. -/
theorem minimum_name_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value r) (name : Nat)
    (he : EqE ((frame ns swap left right).eval r) (.name name)) : r = .name name := by
  have hn := (frame_name_deducible_iff ns swap left right restricted name).mp ⟨r, hm.isPublic, he⟩
  have hsize := hm.least (.name name) hn he
  rcases Term.nodeCount_one_cases hsize with ⟨x, rfl⟩ | ⟨v, rfl⟩ | ⟨c, rfl⟩
  · exact congrArg Term.name ((EqE.name_iff _ _).mp he)
  · exact False.elim (frame_handle_not_atom ns swap left right v (.name name) rfl he)
  · exact False.elim (name_not_eqE_const name c he.symm)

/-- Every constant already has a public one-node recipe. Initial handles cannot
supply another one-node minimum with that value. -/
theorem minimum_constant_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value r) (c : Constant)
    (he : EqE ((frame ns swap left right).eval r) (.const c)) : r = .const c := by
  have hsize := hm.least (.const c) trivial he
  rcases Term.nodeCount_one_cases hsize with ⟨x, rfl⟩ | ⟨v, rfl⟩ | ⟨d, rfl⟩
  · exact False.elim (name_not_eqE_const x c he)
  · exact False.elim (frame_handle_not_atom ns swap left right v (.const c) rfl he)
  · exact congrArg Term.const ((EqE.const_iff _ _).mp he)

end ExplainableCrypto.Helios.Symbolic.Historical.General
