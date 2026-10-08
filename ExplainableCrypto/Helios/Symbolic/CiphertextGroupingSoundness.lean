import ExplainableCrypto.Helios.Symbolic.CiphertextGrouping

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

private theorem ac_left_swap (f : Binary) (hf : AC f) (a b c : Term V) :
    BaseEq (.binary f a (.binary f b c)) (.binary f b (.binary f a c)) := by
  exact Combination.evaluate_baseEq_of_indices f hf id
    (a := .mul (.leaf a) (.mul (.leaf b) (.leaf c)))
    (b := .mul (.leaf b) (.mul (.leaf a) (.leaf c)))
    (by simp only [Combination.indices]; ac_rfl)

private theorem ac_right_swap (f : Binary) (hf : AC f) (a b c : Term V) :
    BaseEq (.binary f (.binary f a b) c) (.binary f (.binary f a c) b) := by
  exact Combination.evaluate_baseEq_of_indices f hf id
    (a := .mul (.mul (.leaf a) (.leaf b)) (.leaf c))
    (b := .mul (.mul (.leaf a) (.leaf c)) (.leaf b))
    (by simp only [Combination.indices]; ac_rfl)

private theorem ac_shuffle (f : Binary) (hf : AC f) (a b c d : Term V) :
    BaseEq (.binary f (.binary f a b) (.binary f c d))
      (.binary f (.binary f a c) (.binary f b d)) := by
  exact Combination.evaluate_baseEq_of_indices f hf id
    (a := .mul (.mul (.leaf a) (.leaf b)) (.mul (.leaf c) (.leaf d)))
    (b := .mul (.mul (.leaf a) (.leaf c)) (.mul (.leaf b) (.leaf d)))
    (by simp only [Combination.indices]; ac_rfl)

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat} {restricted : Finset Nat}

namespace CiphertextGroup
variable {handles : Nat}

theorem merge_nonce (ns : Names n) (φ : Frame restricted handles) (a b : CiphertextGroup n handles) :
    BaseEq (.binary .compose (a.nonce ns φ) (b.nonce ns φ)) ((a.merge b).nonce ns φ) := by
  cases a <;> cases b <;>
    simp only [merge, nonce, Frame.eval, Term.subst, combinationNonce, Combination.evaluate]
  all_goals first
    | exact .refl _
    | exact .equation (.comm .compose trivial _ _)
    | exact .equation (.assoc .compose trivial _ _ _)
    | exact (BaseEq.equation (.assoc .compose trivial _ _ _)).symm
    | exact ac_left_swap .compose trivial _ _ _
    | exact ac_right_swap .compose trivial _ _ _
    | exact ac_shuffle .compose trivial _ _ _ _

theorem merge_message (φ : Frame restricted handles) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (a b : CiphertextGroup n handles) :
    BaseEq (.binary .add (a.message φ swap left right) (b.message φ swap left right))
      ((a.merge b).message φ swap left right) := by
  cases a <;> cases b <;>
    simp only [merge, message, Frame.eval, Term.subst, combinationMessage, Combination.evaluate]
  all_goals first
    | exact .refl _
    | exact .equation (.comm .add trivial _ _)
    | exact .equation (.assoc .add trivial _ _ _)
    | exact (BaseEq.equation (.assoc .add trivial _ _ _)).symm
    | exact ac_left_swap .add trivial _ _ _
    | exact ac_right_swap .add trivial _ _ _
    | exact ac_shuffle .add trivial _ _ _ _

theorem merge_public (a b : CiphertextGroup n handles) (ha : a.Public restricted) (hb : b.Public restricted) :
    (a.merge b).Public restricted := by
  cases a <;> cases b <;> simp_all [Public, merge, Term.Public]

theorem merge_budget (a b : CiphertextGroup n handles) :
    (a.merge b).budget ≤ a.budget + b.budget + 1 := by
  cases a <;> cases b <;> simp only [merge, budget, Term.nodeCount] <;> omega

end CiphertextGroup

namespace CiphertextAssembly

theorem keyRecipe_public (t : CiphertextAssembly n) (hp : t.recipe.Public restricted) :
    t.keyRecipe.Public restricted := by
  induction t with
  | constructed => exact hp.1
  | honest => trivial
  | mul a b ia _ => exact ia hp.1

theorem keyRecipe_smaller (t : CiphertextAssembly n) : t.keyRecipe.nodeCount < t.recipe.nodeCount := by
  induction t with
  | constructed => simp only [keyRecipe, recipe, Term.nodeCount]; omega
  | honest i =>
    have h := ((Term.var i.1.succ : Recipe 3).drop i.2.val).nodeCount_pos
    simp only [keyRecipe, recipe, Term.project, Term.nodeCount]
    omega
  | mul a b ia _ => simp only [keyRecipe, recipe, Term.nodeCount]; omega

theorem keyRecipe_value (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (t : CiphertextAssembly n) (key : Ground)
    (hk : t.KeyAgreement ns (frame ns swap left right) key) :
    EqE ((frame ns swap left right).eval t.keyRecipe) key := by
  induction t with
  | constructed => exact hk
  | honest => exact hk
  | mul a b ia _ => exact ia hk.1

theorem group_public (t : CiphertextAssembly n) (hp : t.recipe.Public restricted) :
    t.group.Public restricted := by
  induction t with
  | constructed k r p => exact hp.2
  | honest => trivial
  | mul a b ia ib => exact CiphertextGroup.merge_public _ _ (ia hp.1) (ib hp.2)

theorem group_budget (t : CiphertextAssembly n) : t.group.budget ≤ t.recipe.nodeCount := by
  induction t with
  | constructed k r p =>
    have hk := k.nodeCount_pos
    simp only [group, CiphertextGroup.budget, recipe, Term.nodeCount]
    omega
  | honest i =>
    have hs := ((Term.var i.1.succ : Recipe 3).drop i.2.val).nodeCount_pos
    simp only [group, CiphertextGroup.budget, recipe, Term.project, Term.nodeCount]
    omega
  | mul a b ia ib =>
    have h := CiphertextGroup.merge_budget a.group b.group
    simp only [group, recipe, Term.nodeCount]
    omega

/-- The payload is padded only for a mixed group; the original tree supplies
its strict bound even when grouping changes the tree's size. -/
theorem mixed_observations_smaller (t : CiphertextAssembly n) {r p : Recipe 3}
    {a : Combination (HonestIndex n)} (hg : t.group = .mixed r p a) :
    r.nodeCount < t.recipe.nodeCount ∧
      (Term.binary .add p (.const .zero)).nodeCount < t.recipe.nodeCount := by
  have h := t.group_budget
  rw [hg] at h
  have hr := r.nodeCount_pos
  have hp := p.nodeCount_pos
  simp only [CiphertextGroup.budget, Term.nodeCount] at *
  omega

theorem constructed_observations_smaller (t : CiphertextAssembly n) {r p : Recipe 3}
    (hg : t.group = .constructed r p) :
    r.nodeCount < t.recipe.nodeCount ∧ p.nodeCount < t.recipe.nodeCount := by
  have h := t.group_budget
  rw [hg] at h
  simp only [CiphertextGroup.budget] at h
  omega

/-- Full-E ciphertext inversion derives the common key at every constructed
leaf and binds every honest leaf to the frame's public key. -/
theorem key_agreement_of_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (t : CiphertextAssembly n)
    {key nonce message : Ground}
    (he : EqE ((frame ns swap left right).eval t.recipe) (.ternary .penc key nonce message)) :
    t.KeyAgreement ns (frame ns swap left right) key := by
  induction t generalizing nonce message with
  | constructed k r p => exact ((EqE.penc_iff _ _ _ _ _ _).mp he).1
  | honest i =>
    have hv := combination_value ns swap left right (Combination.leaf i)
    exact ((EqE.penc_iff _ _ _ _ _ _).mp (hv.symm.trans he)).1
  | mul a b ia ib =>
    obtain ⟨_, _, _, _, ha, hb, _, _⟩ := he.mul_penc_inversion
    exact ⟨ia ha, ib hb⟩

/-- Grouping is sound for arbitrary tree shape, repeated factors, reducible
subrecipes and keys that agree only under E. -/
theorem grouped_value (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (t : CiphertextAssembly n) (key : Ground)
    (hk : t.KeyAgreement ns (frame ns swap left right) key) :
    EqE ((frame ns swap left right).eval t.recipe)
      (.ternary .penc key (t.group.nonce ns (frame ns swap left right))
        (t.group.message (frame ns swap left right) swap left right)) := by
  induction t with
  | constructed k r p => exact .ternary .penc hk (.refl _) (.refl _)
  | honest i =>
    exact (combination_value ns swap left right (.leaf i)).trans
      (.ternary .penc hk (.refl _) (.refl _))
  | mul a b ia ib =>
    exact (EqE.binary .mul (ia hk.1) (ib hk.2)).trans
      ((RootStep.homomorphic _ _ _ _ _).sound.trans
        (.ternary .penc (.refl _) (CiphertextGroup.merge_nonce ns _ _ _).sound
          (CiphertextGroup.merge_message _ swap left right _ _).sound))

end CiphertextAssembly

/-- Exact assembly syntax is recovered from the existing minimum-origin theorem;
no arbitrary constant-value or selector leaf is admitted. -/
theorem assembly_of_ciphertext_syntax (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) {r : Recipe 3} (hs : CiphertextRecipeSyntax r)
    {key nonce message : Ground}
    (he : EqE ((frame ns swap left right).eval r) (.ternary .penc key nonce message)) :
    ∃ t : CiphertextAssembly n, t.recipe = r := by
  induction hs generalizing key nonce message with
  | constructed k r p => exact ⟨.constructed k r p, rfl⟩
  | selected v hc =>
    obtain ⟨i, j, _, hr, _⟩ := frame_projection_ciphertext_origin ns swap left right v hc he
    exact ⟨.honest (i, j), hr.symm⟩
  | mul _ _ ia ib =>
    obtain ⟨_, _, _, _, ha, hb, _, _⟩ := he.mul_penc_inversion
    obtain ⟨a, rfl⟩ := ia ha
    obtain ⟨b, rfl⟩ := ib hb
    exact ⟨.mul a b, rfl⟩

/-- Every minimum ciphertext recipe has a grouped value, preserved caller
publicness, original-size budget, and equations to both supplied components. -/
theorem minimum_ciphertext_grouping (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value r)
    {key nonce message : Ground}
    (he : EqE ((frame ns swap left right).eval r) (.ternary .penc key nonce message)) :
    ∃ t : CiphertextAssembly n, t.recipe = r ∧
      t.KeyAgreement ns (frame ns swap left right) key ∧ t.group.Public restricted ∧
      t.group.budget ≤ r.nodeCount ∧
      t.keyRecipe.Public restricted ∧ t.keyRecipe.nodeCount < r.nodeCount ∧
      EqE ((frame ns swap left right).eval t.keyRecipe) key ∧
      EqE (t.group.nonce ns (frame ns swap left right)) nonce ∧
      EqE (t.group.message (frame ns swap left right) swap left right) message := by
  obtain ⟨t, rfl⟩ := assembly_of_ciphertext_syntax ns swap left right
    (minimum_ciphertext_syntax ns swap left right restricted r hm he) he
  have hk := t.key_agreement_of_value ns swap left right he
  have hv := (EqE.penc_iff _ _ _ _ _ _).mp ((t.grouped_value ns swap left right key hk).symm.trans he)
  exact ⟨t, rfl, hk, t.group_public hm.isPublic, t.group_budget,
    t.keyRecipe_public hm.isPublic, t.keyRecipe_smaller, t.keyRecipe_value ns swap left right key hk, hv.2.1, hv.2.2⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General
