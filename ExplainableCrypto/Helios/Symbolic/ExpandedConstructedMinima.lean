import ExplainableCrypto.Helios.Symbolic.AssemblyCompressionTools
import ExplainableCrypto.Helios.Symbolic.ExpandedCiphertextAssembly

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n handles : Nat} {restricted : Finset Nat}

/-- Opaque nonce-factor protection excludes every honest contribution from a
group equal to an evaluated public nonce. Freshness and group publicness are
unnecessary for this provenance statement. -/
theorem CiphertextGroup.constructed_of_public_nonce_of_opaque (g : CiphertextGroup n handles)
    (ns : Names n) (φ : Frame restricted handles) (hφ : φ.OpaqueProtected)
    (hnames : ∀ i : HonestIndex n, ns.nonce i.1 i.2 ∈ restricted)
    (r : Recipe handles) (hr : r.Public restricted) (he : EqE (g.nonce ns φ) (φ.eval r)) :
    ∃ u v, g = .constructed u v := by
  cases g with
  | constructed u v => exact ⟨u,v,rfl⟩
  | honest a =>
    obtain ⟨i,hi⟩ := a.exists_index
    have hmem : (Term.name (V := Empty) (ns.nonce i.1 i.2)).baseClass ∈ (combinationNonce ns a).composeFactors := by
      rw [combinationNonce,Combination.named_nonce_factors]
      exact Multiset.mem_map.mpr ⟨i,hi,rfl⟩
    exact False.elim (hφ.name_factor_not_deducible r hr (hnames i) _ hmem he.symm)
  | mixed u v a =>
    obtain ⟨i,hi⟩ := a.exists_index
    have hmem : (Term.name (V := Empty) (ns.nonce i.1 i.2)).baseClass ∈
        (Term.binary .compose (φ.eval u) (combinationNonce ns a)).composeFactors := by
      apply Multiset.mem_add.mpr
      right
      rw [combinationNonce,Combination.named_nonce_factors]
      exact Multiset.mem_map.mpr ⟨i,hi,rfl⟩
    exact False.elim (hφ.name_factor_not_deducible r hr (hnames i) _ hmem he.symm)

/-- Constructor minimum closure over actual published handles. All public
competitors are considered; numeric origins and opaque nonce protection
exclude cheaper honest/mixed encodings. -/
theorem expanded_minimum_penc_of_children (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (a b c : Recipe (ExpandedHandles n))
    (ha : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value a)
    (hb : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value b)
    (hc : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value c) :
    MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (.ternary .penc a b c) := by
  have hpublic : (Term.ternary .penc a b c).Public ns.restricted := ⟨ha.isPublic,hb.isPublic,hc.isPublic⟩
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (expandedFrame ns swap left right rs).value) _ hpublic
  obtain ⟨t,rfl,hpub,_,hkeypub,_⟩ := expanded_minimum_ciphertext_assembly ns swap left right rs hn m hm ⟨_,_,_,he.symm⟩
  have hv := expanded_assembly_grouped_value ns swap left right rs t ⟨_,_,_,he.symm⟩
  have hparts := (EqE.penc_iff _ _ _ _ _ _).mp (hv.symm.trans he.symm)
  obtain ⟨r,p,hg⟩ := t.group.constructed_of_public_nonce_of_opaque ns _
    (expanded_frame_opaque_protected ns swap left right rs hp)
    (fun i => Finset.mem_union_right _ (ns.nonce_mem_nonceNames i.1 i.2)) b hb.isPublic hparts.2.1
  have hbudget := t.key_group_budgetWith expandedOld
  rw [hg] at hbudget hpub hparts
  have hkeysize := ha.least (t.keyRecipeWith expandedOld) hkeypub hparts.1.symm
  have hnoncesize := hb.least r hpub.1 hparts.2.1.symm
  have hmessagesize := hc.least p hpub.2 hparts.2.2.symm
  exact hm.of_equivalent_size hpublic he (by
    simp only [CiphertextGroup.budget,Term.nodeCount] at hbudget ⊢
    omega)

/-- Acceptance supplies numeric origins for constructor minimum closure. -/
theorem accepted_expanded_minimum_penc_of_children (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (a b c : Recipe (ExpandedHandles n))
    (ha : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value a)
    (hb : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value b)
    (hc : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value c) :
    MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (.ternary .penc a b c) :=
  expanded_minimum_penc_of_children ns swap left right rs hp
    (accepted_expanded_results_numeric ns hf left right rs hp haccept swap) a b c ha hb hc

/-- Constructor local transport needs no smaller observations or minima: the
original constructor is already a source minimum. -/
theorem accepted_expanded_minimum_children_penc_shared (ns : Names n) (hf : ns.Fresh)
    (swap swap' : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (haccept : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (a b c : Recipe (ExpandedHandles n))
    (ha : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value a)
    (hb : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value b)
    (hc : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value c) :
    Frame.SharedMinimum (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs) (.ternary .penc a b c) :=
  .of_minimal (accepted_expanded_minimum_penc_of_children ns hf swap left right rs hp haccept a b c ha hb hc)

end ExplainableCrypto.Helios.Symbolic.Historical.General
