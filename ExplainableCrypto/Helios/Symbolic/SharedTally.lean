import ExplainableCrypto.Helios.Symbolic.AcceptedSequences
import ExplainableCrypto.Helios.Symbolic.SPOT

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

def tallyPlaintext (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (ds : List (SharedBallotData ns)) (j : Fin (n+1)) : Ground :=
  ds.foldl (fun acc d => .binary .add acc (.const (d.bits j)))
    (.binary .add ((choice swap left right 0).value j) ((choice swap left right 1).value j))

def tallyNonce (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (ds : List (SharedBallotData ns)) (j : Fin (n+1)) : Ground :=
  ds.foldl (fun acc d => .binary .compose acc ((frame ns swap left right).eval (d.nonces j)))
    (.binary .compose (.name (ns.nonce 0 j)) (.name (ns.nonce 1 j)))

/-- The list relation retains the exact recipe/data correspondence through
each homomorphic multiplication; repeated syntax is not deduplicated. -/
theorem fold_tally_ciphertexts (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) (ds : List (SharedBallotData ns))
    (h : List.Forall₂ (fun r d => d.Explains ns left right r) rs ds)
    (j : Fin (n+1)) (acc : Recipe 3) (nr p : Ground)
    (ha : EqE ((frame ns swap left right).eval acc) (.ternary .penc (publicKey ns) nr p)) :
    EqE ((frame ns swap left right).eval (rs.foldl (fun acc r => .binary .mul acc (r.project j.val)) acc))
      (.ternary .penc (publicKey ns)
        (ds.foldl (fun acc d => .binary .compose acc ((frame ns swap left right).eval (d.nonces j))) nr)
        (ds.foldl (fun acc d => .binary .add acc (.const (d.bits j))) p)) := by
  induction h generalizing acc nr p with
  | nil => exact ha
  | @cons r d rs ds hd _ ih =>
    apply ih (.binary .mul acc (r.project j.val))
      (.binary .compose nr ((frame ns swap left right).eval (d.nonces j)))
      (.binary .add p (.const (d.bits j)))
    have he := (EqE.binary .mul ha (hd swap j)).trans (RootStep.homomorphic _ _ _ _ _).sound
    simpa only [Frame.eval,Term.subst,Term.subst_project] using he

/-- The actual candidate aggregate has exactly the shared literal adversarial
contributions and the two honest contributions, with the full nonce fold. -/
theorem tally_ciphertext_of_common_data (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (ds : List (SharedBallotData ns))
    (h : List.Forall₂ (fun r d => d.Explains ns left right r) rs ds) (j : Fin (n+1)) :
    EqE (tallyCiphertext ns swap left right rs j)
      (.ternary .penc (publicKey ns) (tallyNonce ns swap left right ds j)
        (tallyPlaintext ns swap left right ds j)) := by
  apply fold_tally_ciphertexts ns swap left right rs ds h j
  have component (i : Fin 2) : EqE ((frame ns swap left right).eval ((Term.var i.succ).project j.val))
      (ciphertext ns i (choice swap left right i).value j) := by
    simpa only [Frame.eval,Term.subst_project,Term.subst,frame_voter_handle] using
      ballot_project_ciphertext ns i (choice swap left right i).value j
  exact (EqE.binary .mul (component 0) (component 1)).trans (RootStep.homomorphic _ _ _ _ _).sound

/-- E6 decrypts the whole aggregate via the actual matching partial, rather
than postulating that a tally is already the sum of its plaintexts. -/
theorem tally_result_of_common_data (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (ds : List (SharedBallotData ns))
    (h : List.Forall₂ (fun r d => d.Explains ns left right r) rs ds) (j : Fin (n+1)) :
    EqE (tallyResult ns swap left right rs j) (tallyPlaintext ns swap left right ds j) := by
  have hc := tally_ciphertext_of_common_data ns swap left right rs ds h j
  exact (EqE.binary .dec (.binary .partialDecrypt (.refl _) hc) hc).trans
    (RootStep.partial_decrypt _ _ _).sound

/-- Shared adversarial bits permit swapping the two honest summands. Their
possibly different nonce values play no role in this plaintext equality. -/
theorem tally_plaintext_swap (ns : Names n) (left right : CandidateSubstitution n Empty)
    (ds : List (SharedBallotData ns)) (j : Fin (n+1)) :
    EqE (tallyPlaintext ns false left right ds j) (tallyPlaintext ns true left right ds j) := by
  simpa [tallyPlaintext,choice,List.foldl_map] using
    honest_tally_swap (left.value j) (right.value j) (ds.map (fun d => .const (d.bits j)))

private theorem bit_numeric {p : Ground} (h : BitValue p) :
    ∃ k : Nat, k ≤ 1 ∧ EqE p (addNumeral k) := by
  rcases h with hz | ho
  · exact ⟨0,by omega,hz⟩
  · exact ⟨1,by omega,ho.trans (EqE.equation .zero_one).symm⟩

private theorem fold_numeric (ns : Names n) (ds : List (SharedBallotData ns)) (j : Fin (n+1))
    (p : Ground) (k : Nat) (hp : EqE p (addNumeral k)) :
    ∃ out, out ≤ k + ds.length ∧
      EqE (ds.foldl (fun acc d => .binary .add acc (.const (d.bits j))) p) (addNumeral out) := by
  induction ds generalizing p k with
  | nil => exact ⟨k,by simp,hp⟩
  | cons d ds ih =>
    have hb : BitValue (Term.const (d.bits j) : Ground) := by
      rcases d.isBit j with h | h
      · exact Or.inl (h ▸ .refl _)
      · exact Or.inr (h ▸ .refl _)
    obtain ⟨q,hq,he⟩ := bit_numeric hb
    obtain ⟨out,hout,ho⟩ := ih (.binary .add p (.const (d.bits j))) (k+q)
      ((EqE.add_numeral_iff _ _ _).mpr ⟨k,q,rfl,hp,he⟩)
    exact ⟨out,by simp only [List.length_cons]; omega,ho⟩

/-- Candidate validity gives a natural-number result bounded by the number
of voters, without imposing exactly-one voting or a saturating addition law. -/
theorem tally_plaintext_numeric (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (ds : List (SharedBallotData ns)) (j : Fin (n+1)) :
    ∃ k, k ≤ ds.length+2 ∧ EqE (tallyPlaintext ns swap left right ds j) (addNumeral k) := by
  obtain ⟨a,ha,hea⟩ := bit_numeric ((choice swap left right 0).valid.component_bit j)
  obtain ⟨b,hb,heb⟩ := bit_numeric ((choice swap left right 1).valid.component_bit j)
  obtain ⟨out,hout,ho⟩ := fold_numeric ns ds j _ (a+b)
    ((EqE.add_numeral_iff _ _ _).mpr ⟨a,b,rfl,hea,heb⟩)
  exact ⟨out,by omega,ho⟩

/-- Source Lemma 11 for any finite accepted sequence of public submissions.
One bounded natural numeral is the actual E6 result in both initial worlds.
Final-frame static equivalence is not a premise or a conclusion here. -/
theorem accepted_sequence_tally_numeric (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (j : Fin (n+1)) :
    ∃ k, k ≤ rs.length+2 ∧ ∀ swap : Bool, EqE (tallyResult ns swap left right rs j) (addNumeral k) := by
  have hb : ∀ i : Fin 2, (Term.var i.succ : Recipe 3) ∈ honestBoardRecipes := by
    intro i
    fin_cases i <;> simp [honestBoardRecipes]
  obtain ⟨ds,hds⟩ := accepted_sequence_common_data ns hf left right honestBoardRecipes rs hb hp ha
  obtain ⟨k,hk,hnum⟩ := tally_plaintext_numeric ns false left right ds j
  refine ⟨k,?_,?_⟩
  · have hlen := hds.length_eq
    omega
  · intro swap
    cases swap with
    | false => exact (tally_result_of_common_data ns false left right rs ds hds j).trans hnum
    | true =>
      exact (tally_result_of_common_data ns true left right rs ds hds j).trans
        ((tally_plaintext_swap ns left right ds j).symm.trans hnum)

theorem accepted_sequence_tally_swap (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (j : Fin (n+1)) :
    EqE (tallyResult ns false left right rs j) (tallyResult ns true left right rs j) := by
  obtain ⟨_,_,he⟩ := accepted_sequence_tally_numeric ns hf left right rs hp ha j
  exact (he false).trans (he true).symm

end ExplainableCrypto.Helios.Symbolic.Historical.General
