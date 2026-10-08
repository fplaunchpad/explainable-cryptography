import ExplainableCrypto.Helios.Symbolic.HistoricalAggregation
import ExplainableCrypto.Helios.Symbolic.ProofCheckPaths

/-! Semantic witnesses for accepted ballot fields. These values need not be
publicly deducible recipes; Lemma 9's recipe reconstruction is a separate step. -/
namespace ExplainableCrypto.Helios.Symbolic
open Historical
variable {V : Type} {n : Nat}

private theorem foldl_values {α : Type} (xs : List α) (f : Binary) (a b : Term V)
    (left right : α → Term V) (h : EqE a b) (hx : ∀ j, EqE (left j) (right j)) :
    EqE (xs.foldl (fun acc j => .binary f acc (left j)) a)
      (xs.foldl (fun acc j => .binary f acc (right j)) b) := by
  induction xs generalizing a b with
  | nil => exact h
  | cons j xs ih => exact ih _ _ (.binary f h (hx j))

/-- The aggregate retains every component nonce and plaintext, including repeats. -/
theorem aggregateCiphertext_values (key ballot : Term V)
    (rs ms : Fin (n + 1) → Term V)
    (hc : ∀ j, EqE (ballot.project j.val) (.ternary .penc key (rs j) (ms j))) :
    EqE (aggregateCiphertext n ballot)
      (.ternary .penc key (foldCandidates .compose rs) (foldCandidates .add ms)) := by
  apply EqE.trans _ (foldCandidates_ciphertexts key rs ms)
  exact foldl_values (List.finRange n) .mul _ _ _ _ (hc 0) (fun j => hc j.succ)

/-- Definition 4's candidate condition uses a nonempty zero-or-one sum. -/
def CandidateValues (ms : Fin (n + 1) → Term V) : Prop :=
  EqE (foldCandidates .add ms) (.const .zero) ∨
    EqE (foldCandidates .add ms) (.const .one)

/-- The aggregate check restricts any independently identified component plaintexts. -/
theorem ProofValid.candidate_of_ciphertexts {key ballot : Term V}
    (h : ProofValid n key ballot) (rs ms : Fin (n + 1) → Term V)
    (hc : ∀ j, EqE (ballot.project j.val) (.ternary .penc key (rs j) (ms j))) :
    CandidateValues ms := by
  obtain ⟨r, bit, hb, ha, _⟩ := (EqE.check_ok_iff_components _ _ _).mp h.1
  have hv := aggregateCiphertext_values key ballot rs ms hc
  have he := ((EqE.penc_iff _ _ _ _ _ _).mp (hv.symm.trans ha)).2.2
  rcases hb with rfl | rfl
  · exact Or.inl he
  · exact Or.inr he

/-- Exact semantic values of all checked fields; no recipe-publicness claim. -/
structure BallotValues (n : Nat) (key ballot : Term V) where
  nonce : Fin (n + 1) → Term V
  bit : Fin (n + 1) → Constant
  isBit : ∀ j, bit j = .zero ∨ bit j = .one
  ciphertext : ∀ j, EqE (ballot.project j.val) (.ternary .penc key (nonce j) (.const (bit j)))
  componentProof : ∀ j, EqE (ballot.project (n + 1 + j.val))
    (.spk key (nonce j) (.const (bit j)) (ballot.project j.val))
  candidate : CandidateValues (V := V) (fun j => .const (bit j))
  aggregateProof : EqE (ballot.project (2 * (n + 1)))
    (.spk key (foldCandidates .compose nonce) (foldCandidates .add (fun j => .const (bit j)))
      (aggregateCiphertext n ballot))

/-- Validity alone determines all checked values, for arbitrary reducible inputs. -/
theorem proofValid_iff_values (key ballot : Term V) :
    ProofValid n key ballot ↔ Nonempty (BallotValues n key ballot) := by
  constructor
  · intro h
    have hcs := fun j => (EqE.check_ok_iff_components _ _ _).mp (h.2 j)
    choose rs bs hbit hc hp using hcs
    obtain ⟨r, bit, hb, ha, hpa⟩ := (EqE.check_ok_iff_components _ _ _).mp h.1
    have hv := aggregateCiphertext_values key ballot rs (fun j => .const (bs j)) hc
    have he := (EqE.penc_iff _ _ _ _ _ _).mp (hv.symm.trans ha)
    refine ⟨⟨rs, bs, hbit, hc, hp, ?_, ?_⟩⟩
    · rcases hb with rfl | rfl
      · exact Or.inl he.2.2
      · exact Or.inr he.2.2
    · exact hpa.trans (.spk (.refl _) he.2.1.symm he.2.2.symm (.refl _))
  · rintro ⟨v⟩
    constructor
    · have hv := aggregateCiphertext_values key ballot v.nonce (fun j => .const (v.bit j)) v.ciphertext
      rcases v.candidate with hm | hm
      · exact (EqE.check_ok_iff_components _ _ _).mpr
          ⟨_, .zero, Or.inl rfl,
            hv.trans (.ternary .penc (.refl _) (.refl _) hm),
            v.aggregateProof.trans (.spk (.refl _) (.refl _) hm (.refl _))⟩
      · exact (EqE.check_ok_iff_components _ _ _).mpr
          ⟨_, .one, Or.inr rfl,
            hv.trans (.ternary .penc (.refl _) (.refl _) hm),
            v.aggregateProof.trans (.spk (.refl _) (.refl _) hm (.refl _))⟩
    · intro j
      exact (EqE.check_ok_iff_components _ _ _).mpr
        ⟨v.nonce j, v.bit j, v.isBit j, v.ciphertext j, v.componentProof j⟩

theorem accepted_iff_values (key ballot : Term V) (board : List (Term V)) :
    Accepted n key board ballot ↔
      Nonempty (BallotValues n key ballot) ∧ TailGuard n ballot ∧ NoReuse n board ballot := by
  simp only [Accepted, proofValid_iff_values]

/-- A proof accepted for two ciphertexts binds them to the same full E-value. -/
theorem successful_checks_same_proof {k k' c c' p p' : Term V}
    (h : EqE (.ternary .checkspk k c p) (.const .ok))
    (h' : EqE (.ternary .checkspk k' c' p') (.const .ok)) (hp : EqE p p') : EqE c c' := by
  obtain ⟨r, b, _, _, he⟩ := (EqE.check_ok_iff_components _ _ _).mp h
  obtain ⟨r', b', _, _, he'⟩ := (EqE.check_ok_iff_components _ _ _).mp h'
  exact ((EqE.spk_iff _ _ _ _ _ _ _ _).mp (he.symm.trans (hp.trans he'))).2.2.2

/-- Component weeding also excludes every earlier valid component proof. -/
theorem accepted_component_proof_not_reused {key key' ballot earlier : Term V}
    {board : List (Term V)} (ha : Accepted n key board ballot)
    (hm : earlier ∈ board) (hv : ProofValid n key' earlier) (i j : Fin (n + 1)) :
    ¬ EqE (earlier.project (n + 1 + i.val)) (ballot.project (n + 1 + j.val)) := by
  intro hp
  exact ha.2.2 earlier hm i j (successful_checks_same_proof (hv.2 i) (ha.1.2 j) hp)

end ExplainableCrypto.Helios.Symbolic
