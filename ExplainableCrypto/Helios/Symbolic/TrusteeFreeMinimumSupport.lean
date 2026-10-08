import ExplainableCrypto.Helios.Symbolic.TrusteeFreeDestructors

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- An all-position semantic invariant reflects to exact handle support only
for minimum recipes. Successful minimum projections use old honest handles;
whole minimum decryption and proof checking cannot erase their arguments. -/
theorem expanded_minimum_trustee_free_support (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (r : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe restricted (expandedFrame ns swap left right rs).value r)
    (hfree : TrusteeFreeValue ns.secretKey ((expandedFrame ns swap left right rs).eval r)) :
    ∃ s : Recipe (ResultHandles n), r = s.subst (fun i => .var (resultEmbedding i)) := by
  classical
  induction r with
  | name a => exact ⟨.name a, rfl⟩
  | const a => exact ⟨.const a, rfl⟩
  | var v =>
    revert hm hfree
    refine Fin.addCases (fun i => ?_) (fun j => ?_) v
    · intro _ _
      exact ⟨.var (resultOld i), by simp only [Term.subst,result_embedding_old,expandedOld]⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · intro _ hf
        change TrusteeFreeValue ns.secretKey
          ((expandedFrame ns swap left right rs).value (expandedPartial j)) at hf
        rw [expanded_frame_partial] at hf
        exact False.elim (trustee_partial_not_free _ hf)
      · intro _ _
        exact ⟨.var (resultSlot j), by simp only [Term.subst,result_embedding_slot,expandedResult]⟩
  | unary f a ia =>
    have hma := hm.subterm (.unary f .hole)
    suffices ha : ∃ s : Recipe (ResultHandles n), a = s.subst (fun i => .var (resultEmbedding i)) by
      obtain ⟨s,rfl⟩ := ha
      exact ⟨.unary f s,rfl⟩
    cases f with
    | pk => exact ia hma ((TrusteeFreeValue.pk_iff _).mp hfree)
    | fst | snd =>
      by_cases hp : ∃ x y, EqE ((expandedFrame ns swap left right rs).eval a) (.binary .pair x y)
      · obtain ⟨x,y,hp⟩ := hp
        obtain ⟨i,k,_,rfl,_⟩ := expanded_minimum_successful_projection_form ns swap left right rs hn
          restricted _ (by simp) a hm hp
        exact ⟨(Term.var (resultOld i.succ)).drop k,
          by simp only [Term.subst_drop,Term.subst,result_embedding_old]⟩
      · exact ia hma (hfree.projection_of_no_pair _ (by simp) _ (by simpa using hp))
  | binary f a b ia ib =>
    have hma := hm.subterm (.binaryLeft f .hole b)
    have hmb := hm.subterm (.binaryRight f a .hole)
    have hab : TrusteeFreeValue ns.secretKey ((expandedFrame ns swap left right rs).eval a) ∧
        TrusteeFreeValue ns.secretKey ((expandedFrame ns swap left right rs).eval b) := by
      cases f with
      | pair | partialDecrypt =>
        have h := (TrusteeFreeValue.passive_iff _ (by simp) _ _).mp hfree
        exact ⟨h.1,h.2.1⟩
      | add => exact (TrusteeFreeValue.add_iff _ _).mp hfree
      | compose => exact (TrusteeFreeValue.compose_iff _ _).mp hfree
      | mul => exact (TrusteeFreeValue.mul_iff _ _).mp hfree
      | dec =>
        exact hfree.decryption_of_no_match _ _
          (expanded_minimum_decryption_no_match ns swap left right rs hn restricted a b hm)
    obtain ⟨s,rfl⟩ := ia hma hab.1
    obtain ⟨t,rfl⟩ := ib hmb hab.2
    exact ⟨.binary f s t,rfl⟩
  | ternary f a b c ia ib ic =>
    have hma := hm.subterm (.ternaryFirst f .hole b c)
    have hmb := hm.subterm (.ternarySecond f a .hole c)
    have hmc := hm.subterm (.ternaryThird f a b .hole)
    have habc : TrusteeFreeValue ns.secretKey ((expandedFrame ns swap left right rs).eval a) ∧
        TrusteeFreeValue ns.secretKey ((expandedFrame ns swap left right rs).eval b) ∧
        TrusteeFreeValue ns.secretKey ((expandedFrame ns swap left right rs).eval c) := by
      cases f with
      | penc => exact (TrusteeFreeValue.penc_iff _ _ _).mp hfree
      | checkspk => exact hfree.check_of_no_match _ _ _ (hm.no_proof_check_match a b c)
    obtain ⟨s,rfl⟩ := ia hma habc.1
    obtain ⟨t,rfl⟩ := ib hmb habc.2.1
    obtain ⟨u,rfl⟩ := ic hmc habc.2.2
    exact ⟨.ternary f s t u,rfl⟩
  | spk a b c d ia ib ic id =>
    have hf := (TrusteeFreeValue.spk_iff _ _ _ _).mp hfree
    obtain ⟨s,rfl⟩ := ia (hm.subterm (.spkFirst .hole b c d)) hf.1
    obtain ⟨t,rfl⟩ := ib (hm.subterm (.spkSecond _ .hole c d)) hf.2.1
    obtain ⟨u,rfl⟩ := ic (hm.subterm (.spkThird _ _ .hole d)) hf.2.2.1
    obtain ⟨v,rfl⟩ := id (hm.subterm (.spkFourth _ _ _ .hole)) hf.2.2.2
    exact ⟨.spk s t u v,rfl⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General
