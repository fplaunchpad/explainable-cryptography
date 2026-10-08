import ExplainableCrypto.Helios.Symbolic.NumericOffsetEquality
import ExplainableCrypto.Helios.Symbolic.GeneralCandidateProtection

namespace ExplainableCrypto.Helios.Symbolic

/-- Nonempty binary combinations retain every leaf occurrence. There is no unit. -/
inductive Combination (α : Type) where
  | leaf : α → Combination α
  | mul : Combination α → Combination α → Combination α
  deriving DecidableEq, Repr

namespace Combination
variable {α V : Type}

def indices : Combination α → Multiset α
  | .leaf i => {i}
  | .mul a b => a.indices + b.indices

def evaluate (f : Binary) (values : α → Term V) : Combination α → Term V
  | .leaf i => values i
  | .mul a b => .binary f (a.evaluate f values) (b.evaluate f values)

@[reducible] private def acSemigroup (f : Binary) (hf : AC f) : CommSemigroup (BaseClass V) where
  mul a b := Quotient.liftOn₂ a b (fun a b => (Term.binary f a b).baseClass)
    (fun _ _ _ _ ha hb => Quotient.sound (s := baseSetoid V) (.binary f ha hb))
  mul_assoc a b c := Quotient.inductionOn₃ a b c fun a b c =>
    Quotient.sound (s := baseSetoid V) (.equation (.assoc f hf a b c))
  mul_comm a b := Quotient.inductionOn₂ a b fun a b =>
    Quotient.sound (s := baseSetoid V) (.equation (.comm f hf a b))

private theorem evaluate_product (f : Binary) (hf : AC f) (values : α → Term V)
    (t : Combination α) :
    letI := acSemigroup (V := V) f hf
    (t.indices.map (fun i => ((values i).baseClass : WithOne (BaseClass V)))).prod =
      ((t.evaluate f values).baseClass : WithOne (BaseClass V)) := by
  let := acSemigroup (V := V) f hf
  induction t with
  | leaf i => simp [indices, evaluate]
  | mul a b ia ib =>
    rw [indices, Multiset.map_add, Multiset.prod_add, ia, ib]
    rfl

/-- Equal occurrence bags permit any AC evaluation to be rearranged modulo E0.
The adjoined algebraic unit is bookkeeping only; combinations are nonempty. -/
theorem evaluate_baseEq_of_indices (f : Binary) (hf : AC f) (values : α → Term V)
    {a b : Combination α} (h : a.indices = b.indices) :
    BaseEq (a.evaluate f values) (b.evaluate f values) := by
  let := acSemigroup (V := V) f hf
  have hp := congrArg (fun bag : Multiset α =>
    (bag.map (fun i => ((values i).baseClass : WithOne (BaseClass V)))).prod) h
  rw [evaluate_product f hf values a, evaluate_product f hf values b] at hp
  exact (baseClass_eq_iff _ _).mp (WithOne.coe_injective hp)

theorem named_nonce_factors (names : α → Nat) (t : Combination α) :
    (t.evaluate .compose (fun i => (Term.name (V := V) (names i)))).composeFactors =
      t.indices.map (fun i => (Term.name (V := V) (names i)).baseClass) := by
  induction t with
  | leaf i => rfl
  | mul a b ia ib => simp only [evaluate, Term.composeFactors, indices, Multiset.map_add, ia, ib]

theorem named_nonce_irreducible (names : α → Nat) (t : Combination α) :
    Irreducible (t.evaluate .compose (fun i => (Term.name (V := V) (names i)))) := by
  apply irreducible_of_compose_factors
  intro a _ ha
  rw [named_nonce_factors] at ha
  obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp ha
  exact (name_irreducible (names i)).base ((baseClass_eq_iff _ _).mp hi)

/-- Fresh names recover the complete occurrence bag from full-E nonce equality,
including repetition and arbitrary composition-tree rearrangement. -/
theorem named_nonce_eq_iff (names : α → Nat) (hf : Function.Injective names)
    (a b : Combination α) :
    EqE (a.evaluate .compose (fun i => (Term.name (V := V) (names i))))
      (b.evaluate .compose (fun i => .name (names i))) ↔ a.indices = b.indices := by
  constructor
  · intro he
    have hb := (irreducible_eqE_iff_base (named_nonce_irreducible names a)
      (named_nonce_irreducible names b)).mp he
    have hm := hb.compose_factors
    rw [named_nonce_factors, named_nonce_factors] at hm
    apply Multiset.map_injective (f := fun i => (Term.name (V := V) (names i)).baseClass) ?_ hm
    intro i j hij
    exact hf ((BaseEq.name_iff _ _).mp ((baseClass_eq_iff _ _).mp hij))
  · intro h
    exact (evaluate_baseEq_of_indices .compose trivial (fun i => .name (names i)) h).sound

/-- A nonempty combination of bit-valued terms has a present numeric sum,
including all-zero combinations. No object-language identity is inserted. -/
theorem evaluate_bit_sum (values : α → Term V) (hv : ∀ i, BitValue (values i))
    (t : Combination α) : ∃ k : Nat, EqE (t.evaluate .add values) (addNumeral k) := by
  induction t with
  | leaf i =>
    rcases hv i with hz | ho
    · exact ⟨0, hz⟩
    · exact ⟨1, ho.trans (BaseEq.equation .zero_one).sound.symm⟩
  | mul a b ia ib =>
    obtain ⟨k, hk⟩ := ia
    obtain ⟨l, hl⟩ := ib
    exact ⟨k + l, (EqE.binary .add hk hl).trans (addNumerals_combine k l).sound⟩

end Combination

namespace Historical.General
abbrev HonestIndex (n : Nat) := Fin 2 × Fin (n + 1)

def combinationRecipe {n : Nat} (t : Combination (HonestIndex n)) : Recipe 3 :=
  t.evaluate .mul (fun ij => (Term.var ij.1.succ).project ij.2.val)

def combinationNonce {n : Nat} (ns : Names n) (t : Combination (HonestIndex n)) : Ground :=
  t.evaluate .compose (fun ij => .name (ns.nonce ij.1 ij.2))

def combinationMessage {n : Nat} (swap : Bool) (left right : CandidateSubstitution n Empty)
    (t : Combination (HonestIndex n)) : Ground :=
  t.evaluate .add (fun ij => (choice swap left right ij.1).value ij.2)

/-- Honest field combinations are public under any name policy. -/
theorem combinationRecipe_public {n : Nat} (restricted : Finset Nat)
    (t : Combination (HonestIndex n)) : (combinationRecipe t).Public restricted := by
  induction t with
  | leaf i => exact (show (Term.var i.1.succ : Recipe 3).Public restricted from trivial).project _
  | mul a b ia ib => exact ⟨ia, ib⟩

/-- Full-E homomorphic value of every nonempty honest-field combination. -/
theorem combination_value {n : Nat} (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (t : Combination (HonestIndex n)) :
    EqE ((frame ns swap left right).eval (combinationRecipe t))
      (.ternary .penc (publicKey ns) (combinationNonce ns t) (combinationMessage swap left right t)) := by
  induction t with
  | leaf i =>
    simpa only [combinationRecipe, Combination.evaluate, Frame.eval, Term.subst_project,
      Term.subst, frame_voter_handle, combinationNonce, combinationMessage, ciphertext] using
      ballot_project_ciphertext ns i.1 (choice swap left right i.1).value i.2
  | mul a b ia ib => exact (EqE.binary .mul ia ib).trans (RootStep.homomorphic _ _ _ _ _).sound

/-- For the honest-ciphertext product grammar, equality is exactly equality of
nonce-index occurrence bags. This is an unbounded grammar result, not full static equivalence. -/
theorem combination_equality_iff_indices {n : Nat} (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (a b : Combination (HonestIndex n)) :
    EqE ((frame ns swap left right).eval (combinationRecipe a))
      ((frame ns swap left right).eval (combinationRecipe b)) ↔ a.indices = b.indices := by
  have ha := combination_value ns swap left right a
  have hb := combination_value ns swap left right b
  constructor
  · intro he
    have hn := ((EqE.penc_iff _ _ _ _ _ _).mp (ha.symm.trans (he.trans hb))).2.1
    exact (Combination.named_nonce_eq_iff (fun ij : HonestIndex n => ns.nonce ij.1 ij.2) hf.2.1 a b).mp hn
  · intro he
    have hn := Combination.evaluate_baseEq_of_indices .compose trivial
      (fun ij : HonestIndex n => (Term.name (ns.nonce ij.1 ij.2) : Ground)) he
    have hm := Combination.evaluate_baseEq_of_indices .add trivial
      (fun ij : HonestIndex n => (choice swap left right ij.1).value ij.2) he
    exact ha.trans ((EqE.ternary .penc (.refl _) hn.sound hm.sound).trans hb.symm)

theorem combination_equality_swap {n : Nat} (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (a b : Combination (HonestIndex n)) :
    EqE ((frame ns false left right).eval (combinationRecipe a))
      ((frame ns false left right).eval (combinationRecipe b)) ↔
    EqE ((frame ns true left right).eval (combinationRecipe a))
      ((frame ns true left right).eval (combinationRecipe b)) :=
  (combination_equality_iff_indices ns hf false left right a b).trans
    (combination_equality_iff_indices ns hf true left right a b).symm

theorem combinationMessage_numeric {n : Nat} (swap : Bool)
    (left right : CandidateSubstitution n Empty) (t : Combination (HonestIndex n)) :
    ∃ k : Nat, EqE (combinationMessage swap left right t) (addNumeral k) :=
  Combination.evaluate_bit_sum (fun ij : HonestIndex n => (choice swap left right ij.1).value ij.2)
    (fun ij => (choice swap left right ij.1).valid.component_bit ij.2) t

/-- Comparing two fixed payloads after adding the same nonempty honest
combination is invariant under the vote swap, even if that hidden sum changes.
This local message equality does not classify arbitrary public recipe values. -/
theorem combination_offset_equality_swap {n : Nat}
    (left right : CandidateSubstitution n Empty) (t : Combination (HonestIndex n)) (p q : Ground) :
    EqE (.binary .add p (combinationMessage false left right t))
      (.binary .add q (combinationMessage false left right t)) ↔
    EqE (.binary .add p (combinationMessage true left right t))
      (.binary .add q (combinationMessage true left right t)) := by
  obtain ⟨k, hk⟩ := combinationMessage_numeric false left right t
  obtain ⟨l, hl⟩ := combinationMessage_numeric true left right t
  have transfer (m : Ground) (i : Nat) (he : EqE m (addNumeral i)) :
      EqE (.binary .add p m) (.binary .add q m) ↔
        EqE (.binary .add p (addNumeral i)) (.binary .add q (addNumeral i)) := by
    have hp := EqE.binary .add (EqE.refl p) he
    have hq := EqE.binary .add (EqE.refl q) he
    exact ⟨fun h => hp.symm.trans (h.trans hq), fun h => hp.trans (h.trans hq.symm)⟩
  exact (transfer _ k hk).trans ((EqE.add_numeric_offset_iff p q k l).trans (transfer _ l hl).symm)

end Historical.General
end ExplainableCrypto.Helios.Symbolic
