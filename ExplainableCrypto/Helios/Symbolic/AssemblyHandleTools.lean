import ExplainableCrypto.Helios.Symbolic.AssemblyHandleSyntax

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.CiphertextAssembly
variable {n handles : Nat} {restricted : Finset Nat}

theorem keyRecipeWith_public (t : CiphertextAssembly n handles) (old : Fin 3 → Fin handles)
    (hp : (t.recipeWith old).Public restricted) : (t.keyRecipeWith old).Public restricted := by
  induction t with
  | constructed => exact hp.1
  | honest => trivial
  | mul a b ia _ => exact ia hp.1

theorem keyRecipeWith_smaller (t : CiphertextAssembly n handles) (old : Fin 3 → Fin handles) :
    (t.keyRecipeWith old).nodeCount < (t.recipeWith old).nodeCount := by
  induction t with
  | constructed => simp only [keyRecipeWith, recipeWith, Term.nodeCount]; omega
  | honest i =>
    have h := ((Term.var (old i.1.succ) : Recipe handles).drop i.2.val).nodeCount_pos
    simp only [keyRecipeWith, recipeWith, Term.project, Term.nodeCount]
    omega
  | mul a b ia _ => simp only [keyRecipeWith, recipeWith, Term.nodeCount]; omega

theorem group_publicWith (t : CiphertextAssembly n handles) (old : Fin 3 → Fin handles)
    (hp : (t.recipeWith old).Public restricted) : t.group.Public restricted := by
  induction t with
  | constructed => exact hp.2
  | honest => trivial
  | mul a b ia ib => exact CiphertextGroup.merge_public _ _ (ia hp.1) (ib hp.2)

theorem group_budgetWith (t : CiphertextAssembly n handles) (old : Fin 3 → Fin handles) :
    t.group.budget ≤ (t.recipeWith old).nodeCount := by
  induction t with
  | constructed k r p =>
    have hk := k.nodeCount_pos
    simp only [group, CiphertextGroup.budget, recipeWith, Term.nodeCount]
    omega
  | honest i =>
    have h := ((Term.var (old i.1.succ) : Recipe handles).drop i.2.val).nodeCount_pos
    simp only [group, CiphertextGroup.budget, recipeWith, Term.project, Term.nodeCount]
    omega
  | mul a b ia ib =>
    have h := CiphertextGroup.merge_budget a.group b.group
    simp only [group, recipeWith, Term.nodeCount]
    omega

/-- The key equation needs only the retained election-key handle equation. -/
theorem keyRecipeWith_value (ns : Names n) (φ : Frame restricted handles)
    (old : Fin 3 → Fin handles) (hkey : EqE (φ.eval (.var (old 0))) (publicKey ns))
    (t : CiphertextAssembly n handles) (key : Ground) (hk : t.KeyAgreement ns φ key) :
    EqE (φ.eval (t.keyRecipeWith old)) key := by
  induction t with
  | constructed => exact hk
  | honest => exact hkey.trans hk
  | mul a b ia _ => exact ia hk.1

/-- Actual selector values suffice to derive every leaf's common key. -/
theorem key_agreement_of_valueWith (ns : Names n) (φ : Frame restricted handles)
    (old : Fin 3 → Fin handles) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (hhonest : ∀ i : HonestIndex n, EqE (φ.eval ((Term.var (old i.1.succ)).project i.2.val))
      (ciphertext ns i.1 (choice swap left right i.1).value i.2))
    (t : CiphertextAssembly n handles) {key nonce message : Ground}
    (he : EqE (φ.eval (t.recipeWith old)) (.ternary .penc key nonce message)) :
    t.KeyAgreement ns φ key := by
  induction t generalizing nonce message with
  | constructed => exact ((EqE.penc_iff _ _ _ _ _ _).mp he).1
  | honest i => exact ((EqE.penc_iff _ _ _ _ _ _).mp ((hhonest i).symm.trans he)).1
  | mul a b ia ib =>
    obtain ⟨_,_,_,_,ha,hb,_,_⟩ := he.mul_penc_inversion
    exact ⟨ia ha,ib hb⟩

/-- Generic assembly interpretation uses the existing E3 rule and group merge
laws. It allows repeated honest factors and arbitrary constructed subrecipes. -/
theorem grouped_valueWith (ns : Names n) (φ : Frame restricted handles)
    (old : Fin 3 → Fin handles) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (hhonest : ∀ i : HonestIndex n, EqE (φ.eval ((Term.var (old i.1.succ)).project i.2.val))
      (ciphertext ns i.1 (choice swap left right i.1).value i.2))
    (t : CiphertextAssembly n handles) (key : Ground) (hk : t.KeyAgreement ns φ key) :
    EqE (φ.eval (t.recipeWith old))
      (.ternary .penc key (t.group.nonce ns φ) (t.group.message φ swap left right)) := by
  induction t with
  | constructed => exact .ternary .penc hk (.refl _) (.refl _)
  | honest i => exact (hhonest i).trans (.ternary .penc hk (.refl _) (.refl _))
  | mul a b ia ib =>
    exact (EqE.binary .mul (ia hk.1) (ib hk.2)).trans
      ((RootStep.homomorphic _ _ _ _ _).sound.trans
        (.ternary .penc (.refl _) (CiphertextGroup.merge_nonce ns φ _ _).sound
          (CiphertextGroup.merge_message φ swap left right _ _).sound))

end ExplainableCrypto.Helios.Symbolic.Historical.General.CiphertextAssembly
