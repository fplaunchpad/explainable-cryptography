import ExplainableCrypto.Helios.Symbolic.CandidateSubstitutions

/-! Historical ballot constructors for the full source candidate-substitution
parameter. The selected-index family remains an exact specialization. -/
namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

def ciphertext (ns : Names n) (i : Fin 2) (values : Fin (n + 1) → Ground) (j : Fin (n + 1)) : Ground :=
  .ternary .penc (publicKey ns) (.name (ns.nonce i j)) (values j)

def componentProof (ns : Names n) (i : Fin 2) (values : Fin (n + 1) → Ground) (j : Fin (n + 1)) : Ground :=
  .spk (publicKey ns) (.name (ns.nonce i j)) (values j) (ciphertext ns i values j)

def aggregateProof (ns : Names n) (i : Fin 2) (values : Fin (n + 1) → Ground) : Ground :=
  .spk (publicKey ns) (foldCandidates .compose (fun j => .name (ns.nonce i j)))
    (foldCandidates .add values) (foldCandidates .mul (ciphertext ns i values))

def ballotFields (ns : Names n) (i : Fin 2) (values : Fin (n + 1) → Ground) : List Ground :=
  (List.finRange (n + 1)).map (ciphertext ns i values) ++
    (List.finRange (n + 1)).map (componentProof ns i values) ++ [aggregateProof ns i values]

def ballot (ns : Names n) (i : Fin 2) (values : Fin (n + 1) → Ground) : Ground :=
  Term.tuple (ballotFields ns i values)

def choice (swap : Bool) (left right : CandidateSubstitution n Empty) (i : Fin 2) : CandidateSubstitution n Empty :=
  if i.val = 0 then (if swap then right else left) else (if swap then left else right)

def frame (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty) : Frame ns.restricted 3 :=
  ⟨fun h => if h.val = 0 then publicKey ns
    else if h.val = 1 then ballot ns 0 (choice swap left right 0).value
    else ballot ns 1 (choice swap left right 1).value⟩

theorem ballot_fields_length (ns : Names n) (i : Fin 2) (values : Fin (n + 1) → Ground) :
    (ballotFields ns i values).length = fieldCount n := by
  simp [ballotFields, fieldCount]
  omega

theorem ballot_project_ciphertext (ns : Names n) (i : Fin 2) (values : Fin (n + 1) → Ground) (j : Fin (n + 1)) :
    EqE ((ballot ns i values).project j.val) (ciphertext ns i values j) := by
  have h := project_tuple_get (ballotFields ns i values) j.val
    (by rw [ballot_fields_length]; unfold fieldCount; omega)
  simpa [ballot, ballotFields, List.getElem_append, j.isLt] using h

theorem ballot_project_proof (ns : Names n) (i : Fin 2) (values : Fin (n + 1) → Ground) (j : Fin (n + 1)) :
    EqE ((ballot ns i values).project (n + 1 + j.val)) (componentProof ns i values j) := by
  have h := project_tuple_get (ballotFields ns i values) (n + 1 + j.val)
    (by rw [ballot_fields_length]; unfold fieldCount; omega)
  have h₁ : ¬ n + 1 + j.val < n + 1 := by omega
  have h₂ : n + 1 + j.val < n + 1 + (n + 1) := by omega
  simpa [ballot, ballotFields, List.getElem_append, h₁, h₂] using h

theorem ballot_project_aggregate (ns : Names n) (i : Fin 2) (values : Fin (n + 1) → Ground) :
    EqE ((ballot ns i values).project (2 * (n + 1))) (aggregateProof ns i values) := by
  have h := project_tuple_get (ballotFields ns i values) (2 * (n + 1))
    (by rw [ballot_fields_length]; unfold fieldCount; omega)
  have he : 2 * (n + 1) = n + 1 + (n + 1) := by omega
  simpa [ballot, ballotFields, List.getElem_append, he] using h

theorem ballot_tail_guard (ns : Names n) (i : Fin 2) (values : Fin (n + 1) → Ground) :
    TailGuard n (ballot ns i values) := by
  have h := drop_tuple (ballotFields ns i values)
  rw [ballot_fields_length] at h
  exact h

theorem ballot_aggregate_ciphertext (ns : Names n) (i : Fin 2) (values : Fin (n + 1) → Ground) :
    EqE (aggregateCiphertext n (ballot ns i values)) (foldCandidates .mul (ciphertext ns i values)) :=
  foldCandidates_congr .mul _ _ (ballot_project_ciphertext ns i values)

/-- Honest validity uses only the source candidate-sum condition, for arbitrary representatives. -/
theorem honest_proofs_valid (ns : Names n) (i : Fin 2) (values : Fin (n + 1) → Ground)
    (hv : CandidateValues values) : ProofValid n (publicKey ns) (ballot ns i values) := by
  have hagg := ballot_aggregate_ciphertext ns i values
  have hc := hagg.trans (foldCandidates_ciphertexts (publicKey ns) (fun j => .name (ns.nonce i j)) values)
  have hp := (ballot_project_aggregate ns i values).trans
    (EqE.spk (.refl _) (.refl _) (.refl _) hagg.symm)
  constructor
  · rcases hv with hz | ho
    · exact (EqE.check_ok_iff_components _ _ _).mpr ⟨_, .zero, Or.inl rfl,
        hc.trans (.ternary .penc (.refl _) (.refl _) hz),
        hp.trans (.spk (.refl _) (.refl _) hz (.refl _))⟩
    · exact (EqE.check_ok_iff_components _ _ _).mpr ⟨_, .one, Or.inr rfl,
        hc.trans (.ternary .penc (.refl _) (.refl _) ho),
        hp.trans (.spk (.refl _) (.refl _) ho (.refl _))⟩
  · intro j
    have hproj := ballot_project_ciphertext ns i values j
    have hproof := ballot_project_proof ns i values j
    rcases hv.component_bit j with hz | ho
    · exact (EqE.check_ok_iff_components _ _ _).mpr ⟨_, .zero, Or.inl rfl,
        hproj.trans (.ternary .penc (.refl _) (.refl _) hz),
        hproof.trans (.spk (.refl _) (.refl _) hz hproj.symm)⟩
    · exact (EqE.check_ok_iff_components _ _ _).mpr ⟨_, .one, Or.inr rfl,
        hproj.trans (.ternary .penc (.refl _) (.refl _) ho),
        hproof.trans (.spk (.refl _) (.refl _) ho hproj.symm)⟩

theorem honest_empty_board_accepts (ns : Names n) (i : Fin 2) (c : CandidateSubstitution n Empty) :
    Accepted n (publicKey ns) [] (ballot ns i c.value) := by
  refine ⟨honest_proofs_valid ns i c.value c.valid, ballot_tail_guard ns i c.value, ?_⟩
  intro earlier h
  simp at h

theorem fresh_voters_no_reuse (ns : Names n) (hf : ns.Fresh) (i j : Fin 2) (hne : i ≠ j)
    (values values' : Fin (n + 1) → Ground) : NoReuse n [ballot ns i values] (ballot ns j values') := by
  intro earlier hm a b he
  have hm' : earlier = ballot ns i values := by simpa using hm
  subst earlier
  have hc := (ballot_project_ciphertext ns i values a).symm.trans
    (he.trans (ballot_project_ciphertext ns j values' b))
  have hr := ((EqE.penc_iff _ _ _ _ _ _).mp hc).2.1
  have hn := (EqE.name_iff _ _).mp hr
  have hpair : (i, a) = (j, b) := hf.2.1 hn
  exact hne (congrArg Prod.fst hpair)

theorem honest_accepts_after_other (ns : Names n) (hf : ns.Fresh) (i j : Fin 2) (hne : i ≠ j)
    (left right : CandidateSubstitution n Empty) :
    Accepted n (publicKey ns) [ballot ns i left.value] (ballot ns j right.value) :=
  ⟨honest_proofs_valid ns j right.value right.valid, ballot_tail_guard ns j right.value,
    fresh_voters_no_reuse ns hf i j hne left.value right.value⟩

private theorem tuple_congr {as bs : List Ground} (h : List.Forall₂ EqE as bs) :
    EqE (Term.tuple as) (Term.tuple bs) := by
  induction h with
  | nil => exact .refl _
  | cons h _ ih => exact .binary .pair h ih

private theorem map_related {α : Type} (xs : List α) (f g : α → Ground)
    (h : ∀ j, EqE (f j) (g j)) : List.Forall₂ EqE (xs.map f) (xs.map g) := by
  induction xs with
  | nil => exact .nil
  | cons j xs ih => exact .cons (h j) ih

private theorem append_related {as bs cs ds : List Ground}
    (hab : List.Forall₂ EqE as bs) (hcd : List.Forall₂ EqE cs ds) :
    List.Forall₂ EqE (as ++ cs) (bs ++ ds) := by
  induction hab with
  | nil => exact hcd
  | cons h _ ih => exact .cons h ih

/-- Changing only E-equivalent vote representatives preserves the complete ballot value. -/
theorem ballot_congr (ns : Names n) (i : Fin 2) (a b : Fin (n + 1) → Ground)
    (h : ∀ j, EqE (a j) (b j)) : EqE (ballot ns i a) (ballot ns i b) := by
  have hc : ∀ j, EqE (ciphertext ns i a j) (ciphertext ns i b j) := fun j =>
    .ternary .penc (.refl _) (.refl _) (h j)
  have hp : ∀ j, EqE (componentProof ns i a j) (componentProof ns i b j) := fun j =>
    .spk (.refl _) (.refl _) (h j) (hc j)
  have hg : EqE (aggregateProof ns i a) (aggregateProof ns i b) :=
    .spk (.refl _) (.refl _) (foldCandidates_congr .add a b h) (foldCandidates_congr .mul _ _ hc)
  exact tuple_congr (append_related (append_related (map_related _ _ _ hc) (map_related _ _ _ hp)) (.cons hg .nil))

theorem frame_voter_handle (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty) (i : Fin 2) :
    (frame ns swap left right).value i.succ = ballot ns i (choice swap left right i).value := by
  fin_cases i <;> rfl

/-- Pointwise frame equality here changes representations of the same votes only. -/
theorem frame_congr (ns : Names n) (swap : Bool) (left right left' right' : CandidateSubstitution n Empty)
    (hl : ∀ j, EqE (left.value j) (left'.value j)) (hr : ∀ j, EqE (right.value j) (right'.value j)) :
    ∀ h, EqE ((frame ns swap left right).value h) ((frame ns swap left' right').value h) := by
  have hc (i : Fin 2) (j : Fin (n + 1)) :
      EqE ((choice swap left right i).value j) ((choice swap left' right' i).value j) := by
    simp only [choice]
    split_ifs <;> first | exact hl j | exact hr j
  intro h
  fin_cases h
  · exact .refl _
  · exact ballot_congr ns 0 _ _ (hc 0)
  · exact ballot_congr ns 1 _ _ (hc 1)

/-- Arbitrary candidate representatives have a pointwise E-equal literal-bit frame. -/
theorem frame_bit_representatives (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty) :
    ∃ a b : BitCandidate n, ∀ h,
      EqE ((frame ns swap left right).value h) ((frame ns swap a.substitution b.substitution).value h) := by
  obtain ⟨a, ha⟩ := left.bit_representative
  obtain ⟨b, hb⟩ := right.bit_representative
  exact ⟨a, b, frame_congr ns swap left right a.substitution b.substitution ha hb⟩

theorem selected_ballot_specialization (ns : Names n) (i : Fin 2) (chosen : Fin (n + 1)) :
    ballot ns i (BitCandidate.selected chosen).values = Historical.ballot ns i chosen := rfl

theorem selected_frame_specialization (ns : Names n) (swap : Bool) (left right : Fin (n + 1)) :
    (frame ns swap (BitCandidate.selected left).substitution (BitCandidate.selected right).substitution).value =
      (Historical.frame ns swap left right).value := by
  funext h
  fin_cases h <;> cases swap <;> rfl

end ExplainableCrypto.Helios.Symbolic.Historical.General
