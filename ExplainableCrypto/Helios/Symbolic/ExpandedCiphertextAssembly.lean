import ExplainableCrypto.Helios.Symbolic.AssemblyHandleTools
import ExplainableCrypto.Helios.Symbolic.ExpandedCipherKeyTransfer
import ExplainableCrypto.Helios.Symbolic.ExpandedGroupEquality

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Honest assembly leaves use the retained original voter handles. -/
theorem expanded_honest_selector_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (i : HonestIndex n) :
    EqE ((expandedFrame ns swap left right rs).eval
      ((Term.var (expandedOld i.1.succ)).project i.2.val))
      (ciphertext ns i.1 (choice swap left right i.1).value i.2) := by
  rw [Frame.eval, Term.subst_project, Term.subst, expanded_frame_old, frame_voter_handle]
  exact ballot_project_ciphertext ns i.1 (choice swap left right i.1).value i.2

/-- Numeric result origins exclude invented ciphertext leaves at published
slots. The remaining grammar recovers exact assembly syntax. -/
theorem expanded_assembly_of_ciphertext_syntax (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs)
    {r : Recipe (ExpandedHandles n)} (hs : CiphertextRecipeSyntax r)
    {key nonce message : Ground}
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (.ternary .penc key nonce message)) :
    ∃ t : CiphertextAssembly n (ExpandedHandles n), t.recipeWith expandedOld = r := by
  induction hs generalizing key nonce message with
  | constructed k r p => exact ⟨.constructed k r p,rfl⟩
  | selected v hc =>
    obtain ⟨i,j,_,hr,_⟩ := expanded_projection_ciphertext_origin ns swap left right rs hn v hc he
    exact ⟨.honest (i,j),hr.symm⟩
  | mul _ _ ia ib =>
    obtain ⟨_,_,_,_,ha,hb,_,_⟩ := he.mul_penc_inversion
    obtain ⟨a,rfl⟩ := ia ha
    obtain ⟨b,rfl⟩ := ib hb
    exact ⟨.mul a b,rfl⟩

/-- Every actual expanded minimum ciphertext has an exact assembly, a public
bounded group and a strictly smaller public key recipe. -/
theorem expanded_minimum_ciphertext_assembly (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs)
    (r : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (hv : ((expandedFrame ns swap left right rs).eval r).CiphertextValue) :
    ∃ t : CiphertextAssembly n (ExpandedHandles n), t.recipeWith expandedOld = r ∧
      t.group.Public ns.restricted ∧ t.group.budget ≤ r.nodeCount ∧
      (t.keyRecipeWith expandedOld).Public ns.restricted ∧
      (t.keyRecipeWith expandedOld).nodeCount < r.nodeCount := by
  obtain ⟨key,nonce,message,he⟩ := hv
  obtain ⟨t,rfl⟩ := expanded_assembly_of_ciphertext_syntax ns swap left right rs hn
    (expanded_minimum_ciphertext_syntax ns swap left right rs hn ns.restricted r hm he) he
  exact ⟨t,rfl,t.group_publicWith expandedOld hm.isPublic,t.group_budgetWith expandedOld,
    t.keyRecipeWith_public expandedOld hm.isPublic,t.keyRecipeWith_smaller expandedOld⟩

/-- Ciphertext-valued assemblies reduce to their selected key and group in the
actual frame. Common-key agreement is derived from the supplied value. -/
theorem expanded_assembly_grouped_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (t : CiphertextAssembly n (ExpandedHandles n))
    (hv : ((expandedFrame ns swap left right rs).eval (t.recipeWith expandedOld)).CiphertextValue) :
    EqE ((expandedFrame ns swap left right rs).eval (t.recipeWith expandedOld))
      (.ternary .penc ((expandedFrame ns swap left right rs).eval (t.keyRecipeWith expandedOld))
        (t.group.nonce ns (expandedFrame ns swap left right rs))
        (t.group.message (expandedFrame ns swap left right rs) swap left right)) := by
  obtain ⟨key,nonce,message,he⟩ := hv
  have hh := expanded_honest_selector_value ns swap left right rs
  have hk := t.key_agreement_of_valueWith ns _ expandedOld swap left right hh he
  have hkey := t.keyRecipeWith_value ns (expandedFrame ns swap left right rs) expandedOld
    (by rw [expanded_election_handle_value]; exact .refl _) key hk
  exact (t.grouped_valueWith ns _ expandedOld swap left right hh key hk).trans
    (.ternary .penc hkey.symm (.refl _) (.refl _))

/-- Exact recipe equality reduces to the separate public key comparison and
nine-case group observation matrix, retaining opaque published values. -/
theorem expanded_assembly_equality_iff (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (a b : CiphertextAssembly n (ExpandedHandles n))
    (ha : (a.recipeWith expandedOld).Public ns.restricted)
    (hb : (b.recipeWith expandedOld).Public ns.restricted)
    (hva : ((expandedFrame ns swap left right rs).eval (a.recipeWith expandedOld)).CiphertextValue)
    (hvb : ((expandedFrame ns swap left right rs).eval (b.recipeWith expandedOld)).CiphertextValue) :
    EqE ((expandedFrame ns swap left right rs).eval (a.recipeWith expandedOld))
      ((expandedFrame ns swap left right rs).eval (b.recipeWith expandedOld)) ↔
    EqE ((expandedFrame ns swap left right rs).eval (a.keyRecipeWith expandedOld))
      ((expandedFrame ns swap left right rs).eval (b.keyRecipeWith expandedOld)) ∧
      a.group.Observation (expandedFrame ns swap left right rs) b.group := by
  have h₁ := expanded_assembly_grouped_value ns swap left right rs a hva
  have h₂ := expanded_assembly_grouped_value ns swap left right rs b hvb
  have hc := expanded_group_ciphertext_eq_iff ns hf swap left right rs hp a.group b.group
    (a.group_publicWith expandedOld ha) (b.group_publicWith expandedOld hb)
    ((expandedFrame ns swap left right rs).eval (a.keyRecipeWith expandedOld))
    ((expandedFrame ns swap left right rs).eval (b.keyRecipeWith expandedOld))
  exact ⟨fun he => hc.mp (h₁.symm.trans (he.trans h₂)),
    fun he => h₁.trans ((hc.mpr he).trans h₂.symm)⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General
