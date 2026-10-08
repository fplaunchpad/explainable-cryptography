import ExplainableCrypto.Helios.Symbolic.TupleGuard

/-! §5.2.2 ballot predicates. `n` means n+1 candidates, ensuring a nonempty
homomorphic product without introducing an identity absent from E. The corrected
tail guard is authorised and documented separately from the printed formula. -/
namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- There are two fields per candidate and one aggregate proof. -/
def fieldCount (n : Nat) := 2 * (n + 1) + 1

def aggregateCiphertext (n : Nat) (b : Term V) : Term V :=
  (List.finRange n).foldl (fun acc i => .binary .mul acc (b.project (i.val + 1)))
    (b.project 0)

def ProofValid (n : Nat) (key ballot : Term V) : Prop :=
  EqE (.ternary .checkspk key (aggregateCiphertext n ballot)
    (ballot.project (2 * (n + 1)))) (.const .ok) ∧
  ∀ i : Fin (n + 1), EqE (.ternary .checkspk key (ballot.project i.val)
    (ballot.project (n + 1 + i.val))) (.const .ok)

def NoReuse (n : Nat) (board : List (Term V)) (ballot : Term V) : Prop :=
  ∀ earlier ∈ board, ∀ i j : Fin (n + 1),
    ¬ EqE (earlier.project i.val) (ballot.project j.val)

/-- Printed π_(2ℓ+2), retained solely for comparison and regression checks. -/
def PrintedGuard (n : Nat) (ballot : Term V) : Prop :=
  EqE (ballot.project (fieldCount n)) (.const .bottom)

/-- Documented correction: snd^(2ℓ+1), the remaining tail after all fields. -/
def TailGuard (n : Nat) (ballot : Term V) : Prop :=
  EqE (ballot.drop (fieldCount n)) (.const .bottom)

def Accepted (n : Nat) (key : Term V) (board : List (Term V)) (ballot : Term V) : Prop :=
  ProofValid n key ballot ∧ TailGuard n ballot ∧ NoReuse n board ballot

/-- Projections inside the tuple recover exactly the corresponding fields. -/
theorem project_tuple_get (xs : List (Term V)) (i : Nat) (h : i < xs.length) :
    EqE ((Term.tuple xs).project i) xs[i] := by
  induction xs generalizing i with
  | nil => simp at h
  | cons a as ih =>
    cases i with
    | zero => exact .equation (.fst a (Term.tuple as))
    | succ i =>
      exact (EqE.unary .fst ((EqE.equation (.snd a (Term.tuple as))).drop i)).trans
        (ih i (by simpa using h))

/-- Single-candidate ballot: ciphertext, component proof, aggregate proof. -/
def oneCandidateFields (key nonce : Term V) : List (Term V) :=
  let c := Term.ternary .penc key nonce (.const .one)
  let p := Term.spk key nonce (.const .one) c
  [c, p, p]

def oneCandidateBallot (key nonce : Term V) : Term V :=
  Term.tuple (oneCandidateFields key nonce)

theorem oneCandidate_proofs_valid (key nonce : Term V) :
    ProofValid 0 key (oneCandidateBallot key nonce) := by
  let c := Term.ternary .penc key nonce (.const .one)
  let p := Term.spk key nonce (.const .one) c
  have hc := project_tuple_get [c, p, p] 0 (by simp)
  have hp := project_tuple_get [c, p, p] 1 (by simp)
  have ha := project_tuple_get [c, p, p] 2 (by simp)
  constructor
  · exact (EqE.ternary .checkspk (.refl _) hc ha).trans (.equation (.check_one key nonce))
  · intro i
    have hi : i.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)
    simp only [hi, Nat.add_zero]
    exact (EqE.ternary .checkspk (.refl _) hc hp).trans (.equation (.check_one key nonce))

theorem oneCandidate_corrected_accepts (key nonce : Term V) :
    Accepted 0 key [] (oneCandidateBallot key nonce) := by
  refine ⟨oneCandidate_proofs_valid key nonce, ?_, ?_⟩
  · exact drop_tuple (oneCandidateFields key nonce)
  · intro earlier h
    simp at h

theorem oneCandidate_printed_rejects (key nonce : Term V) :
    ¬ PrintedGuard 0 (oneCandidateBallot key nonce) :=
  canonical_tuple_fails_printed_guard (oneCandidateFields key nonce)

/-- Weeding is active: an already-present ballot cannot be accepted again. -/
theorem accepted_excludes_replay (n : Nat) (key ballot : Term V) (board : List (Term V))
    (hmem : ballot ∈ board) : ¬ Accepted n key board ballot := by
  intro h
  exact h.2.2 ballot hmem 0 0 (.refl _)

end ExplainableCrypto.Helios.Symbolic
