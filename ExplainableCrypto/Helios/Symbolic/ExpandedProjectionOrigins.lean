import ExplainableCrypto.Helios.Symbolic.ExpandedMinimumOrigins

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- The actual result values are numeric. Acceptance proves this condition;
it is kept explicit in the reusable origin lemmas. -/
def ExpandedResultsNumeric (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) : Prop :=
  ∀ j : Fin (n+1), ∃ number, EqE (tallyResult ns swap left right rs j) (addNumeral number)

theorem accepted_expanded_results_numeric (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs) (swap : Bool) :
    ExpandedResultsNumeric ns swap left right rs := by
  intro j
  obtain ⟨k,_,hk⟩ := accepted_sequence_tally_numeric ns hf left right rs hp ha j
  exact ⟨k,hk swap⟩

private theorem numeral_not_pair (number : Nat) (x y : Ground) :
    ¬ EqE (addNumeral number) (.binary .pair x y) := by
  intro he
  have hh := (addNumeral_irreducible number).pair_head_of_eq he
  cases number <;> cases hh

private theorem numeral_not_ciphertext (number : Nat) (key nonce message : Ground) :
    ¬ EqE (addNumeral number) (.ternary .penc key nonce message) := by
  intro he
  obtain ⟨_,_,_,hshape,_⟩ := he.symm.penc_irreducible_shape (addNumeral_irreducible number)
  cases number <;> cases hshape

private theorem numeral_not_partial (number : Nat) (key binding : Ground) :
    ¬ EqE (addNumeral number) (.binary .partialDecrypt key binding) := by
  intro he
  obtain ⟨_,_,hshape,_⟩ := he.symm.passive_binary_irreducible_shape (Or.inr rfl) (addNumeral_irreducible number)
  cases number <;> cases hshape

private theorem partial_not_pair (key binding x y : Ground) :
    ¬ EqE (.binary .partialDecrypt key binding) (.binary .pair x y) := by
  intro he
  have hf := ((EqE.passive_binary_iff .partialDecrypt .pair (Or.inr rfl) (Or.inl rfl) _ _ _ _).mp he).1
  cases hf

theorem expanded_handle_not_ciphertext (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (v : Fin (ExpandedHandles n))
    (key nonce message : Ground) :
    ¬ EqE ((expandedFrame ns swap left right rs).value v) (.ternary .penc key nonce message) := by
  refine Fin.addCases (fun i => ?_) (fun k => ?_) v
  · simpa only [expandedFrame,Fin.addCases_left] using frame_handle_not_ciphertext ns swap left right i key nonce message
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simp only [expandedFrame,Fin.addCases_right,Fin.addCases_left]
      exact fun he => penc_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ _ _ he.symm
    · simp only [expandedFrame,Fin.addCases_right]
      obtain ⟨number,hnum⟩ := hn j
      exact fun he => numeral_not_ciphertext number key nonce message (hnum.symm.trans he)

private theorem voter_ciphertext_origin (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (i : Fin 2)
    {r : Recipe (ExpandedHandles n)} (hc : ProjectionChain (expandedOld (n := n) i.succ) r)
    {key nonce message : Ground}
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (.ternary .penc key nonce message)) :
    ∃ j : Fin (n+1), r = (Term.var (expandedOld (n := n) i.succ)).project j.val ∧
      EqE (ciphertext ns i (choice swap left right i).value j) (.ternary .penc key nonce message) := by
  have hv : EqE ((expandedFrame ns swap left right rs).value (expandedOld (n := n) i.succ))
      (Term.tuple (ballotFields ns i (choice swap left right i).value)) := by
    rw [expanded_frame_old,frame_voter_handle]
    exact .refl _
  obtain ⟨idx,hi,hr,hval⟩ := hc.ciphertext_origin _ hv (ballot_fields_not_pair ns i _) he
  rcases ballot_field_cases ns i (choice swap left right i).value idx hi with
    ⟨j,rfl,hfield⟩ | ⟨j,_,hfield⟩ | ⟨_,hfield⟩
  · exact ⟨j,hr,hfield ▸ hval⟩
  · rw [hfield] at hval
    exact False.elim (penc_not_eqE_spk _ _ _ _ _ _ _ hval.symm)
  · rw [hfield] at hval
    exact False.elim (penc_not_eqE_spk _ _ _ _ _ _ _ hval.symm)

/-- New partial and numeric-result handles cannot supply ciphertext selectors.
Every ciphertext-valued chain is still an indexed honest component. -/
theorem expanded_projection_ciphertext_origin (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (v : Fin (ExpandedHandles n))
    {r : Recipe (ExpandedHandles n)} (hc : ProjectionChain v r)
    {key nonce message : Ground}
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (.ternary .penc key nonce message)) :
    ∃ i : Fin 2, ∃ j : Fin (n+1), v = expandedOld (n := n) i.succ ∧
      r = (Term.var (expandedOld (n := n) i.succ)).project j.val ∧
      EqE (ciphertext ns i (choice swap left right i).value j) (.ternary .penc key nonce message) := by
  revert hc he
  refine Fin.addCases (fun old => ?_) (fun extra => ?_) v
  · intro hc he
    fin_cases old
    · exact False.elim (hc.not_ciphertext_of_handle
        (σ := (expandedFrame ns swap left right rs).value)
        (fun x y h => pk_not_eqE_pair _ x y (by simpa [expandedFrame,frame,publicKey] using h))
        (fun k s m => expanded_handle_not_ciphertext ns swap left right rs hn _ k s m) _ _ _ he)
    · obtain ⟨j,hr,hval⟩ := voter_ciphertext_origin ns swap left right rs 0 hc he
      exact ⟨0,j,rfl,hr,hval⟩
    · obtain ⟨j,hr,hval⟩ := voter_ciphertext_origin ns swap left right rs 1 hc he
      exact ⟨1,j,rfl,hr,hval⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) extra
    · intro hc he
      exact False.elim (hc.not_ciphertext_of_handle
        (σ := (expandedFrame ns swap left right rs).value)
        (fun x y h => partial_not_pair _ _ x y (by simpa only [expandedFrame,Fin.addCases_right,Fin.addCases_left,tallyPartial] using h))
        (fun k s m => expanded_handle_not_ciphertext ns swap left right rs hn _ k s m) _ _ _ he)
    · intro hc he
      obtain ⟨number,hnum⟩ := hn j
      exact False.elim (hc.not_ciphertext_of_handle
        (σ := (expandedFrame ns swap left right rs).value)
        (fun x y h => numeral_not_pair number x y (hnum.symm.trans
          (by simpa only [expandedFrame,Fin.addCases_right] using h)))
        (fun k s m => expanded_handle_not_ciphertext ns swap left right rs hn _ k s m) _ _ _ he)

/-- Honest leaf plaintexts are literal bits in the supplied world. The
certificate reuses the existing nonempty product grammar and size theorem. -/
theorem expanded_projection_chain_certificates (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) {r : Recipe (ExpandedHandles n)}
    (hc : ∃ v, ProjectionChain v r) : CiphertextCertificates (expandedFrame ns swap left right rs).value r := by
  intro key nonce message he
  obtain ⟨v,hc⟩ := hc
  obtain ⟨i,j,_,rfl,hval⟩ := expanded_projection_ciphertext_origin ns swap left right rs hn v hc he
  have hkey := ((EqE.penc_iff _ _ _ _ _ _).mp hval).1
  have hcipher : EqE ((expandedFrame ns swap left right rs).eval ((Term.var (expandedOld (n := n) i.succ)).project j.val))
      (ciphertext ns i (choice swap left right i).value j) := by
    rw [Frame.eval,Term.subst_project,Term.subst,expanded_frame_old,frame_voter_handle]
    exact ballot_project_ciphertext ns i (choice swap left right i).value j
  have hsize : 1 < ((Term.var (expandedOld (n := n) i.succ) : Recipe (ExpandedHandles n)).project j.val).nodeCount := by
    have hpos := ((Term.var (expandedOld (n := n) i.succ) : Recipe (ExpandedHandles n)).drop j.val).nodeCount_pos
    simp only [Term.project,Term.nodeCount]
    omega
  have make (bit : Constant) (hbit : EqE ((choice swap left right i).value j) (.const bit)) :
      ∃ p s, CiphertextProduct (expandedFrame ns swap left right rs).value key
        ((Term.var (expandedOld (n := n) i.succ)).project j.val) p s ∧
        CiphertextRecipeSyntax ((Term.var (expandedOld (n := n) i.succ)).project j.val) :=
    ⟨.const bit,.name (ns.nonce i j),
      .constant _ _ bit (hcipher.trans (.ternary .penc hkey (.refl _) hbit)) hsize,
      .selected _ (.project _ j.val)⟩
  rcases (choice swap left right i).valid.component_bit j with hz | ho
  · exact make .zero hz
  · exact make .one ho

private theorem voter_not_partial (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (i : Fin 2)
    {r : Recipe (ExpandedHandles n)} (hc : ProjectionChain (expandedOld i.succ) r) (key binding : Ground) :
    ¬ EqE ((expandedFrame ns swap left right rs).eval r) (.binary .partialDecrypt key binding) := by
  have hv : EqE ((expandedFrame ns swap left right rs).value (expandedOld i.succ))
      (Term.tuple (ballotFields ns i (choice swap left right i).value)) := by
    rw [expanded_frame_old,frame_voter_handle]
    exact .refl _
  exact hc.not_partialDecrypt_of_tuple _ hv (ballot_fields_not_pair ns i _)
    (ballot_fields_not_partialDecrypt ns i _) key binding

/-- Partial-valued selector chains stop at a published partial handle. Neither
its fields nor any old ballot/result selector can supply a new partial value. -/
theorem expanded_projection_partial_origin (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (v : Fin (ExpandedHandles n))
    {r : Recipe (ExpandedHandles n)} (hc : ProjectionChain v r) {key binding : Ground}
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (.binary .partialDecrypt key binding)) :
    ∃ j : Fin (n+1), r = .var (expandedPartial j) := by
  have handle {v : Fin (ExpandedHandles n)} {r : Recipe (ExpandedHandles n)}
      (hc : ProjectionChain v r)
      (hp : ∀ x y, ¬ EqE ((expandedFrame ns swap left right rs).value v) (.binary .pair x y))
      (he : EqE ((expandedFrame ns swap left right rs).eval r) (.binary .partialDecrypt key binding)) :
      r = .var v := by
    cases hc with
    | handle => rfl
    | step f hf hc =>
      obtain ⟨x,y,hpair,_⟩ := he.projection_partialDecrypt_inversion hf
      exact False.elim (hc.not_pair_of_handle hp x y hpair.sound)
  revert hc he
  refine Fin.addCases (fun old => ?_) (fun extra => ?_) v
  · intro hc he
    fin_cases old
    · have hr := handle hc (fun x y h => pk_not_eqE_pair _ x y
        (by simpa [expandedFrame,frame,publicKey] using h)) he
      subst r
      exact False.elim (pk_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _
        (by simpa [Frame.eval,Term.subst,expandedFrame,frame,publicKey] using he))
    · exact False.elim (voter_not_partial ns swap left right rs 0 hc key binding he)
    · exact False.elim (voter_not_partial ns swap left right rs 1 hc key binding he)
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) extra
    · intro hc he
      exact ⟨j,handle hc (fun x y h => partial_not_pair _ _ x y
        (by simpa only [expandedFrame,expandedPartial,Fin.addCases_right,Fin.addCases_left,tallyPartial] using h)) he⟩
    · intro hc he
      obtain ⟨number,hnum⟩ := hn j
      have hr := handle hc (fun x y h => numeral_not_pair number x y
        (hnum.symm.trans (by simpa only [expandedFrame,Fin.addCases_right] using h))) he
      subst r
      exact False.elim (numeral_not_partial number key binding (hnum.symm.trans
        (by simpa only [Frame.eval,Term.subst,expandedFrame,Fin.addCases_right] using he)))

end ExplainableCrypto.Helios.Symbolic.Historical.General
