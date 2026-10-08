import ExplainableCrypto.Helios.Symbolic.Separation

/-! A literal-source mismatch: §5.2.1's tuple/projection encoding and §5.2.2's
next-field guard. The user-authorised tail correction is explicit in Ballot.lean. See docs/research/helios-symbolic-tuple-guard.md. -/
namespace ExplainableCrypto.Helios.Symbolic

namespace Term
variable {V : Type}

def tuple : List (Term V) → Term V
  | [] => .const .bottom
  | a :: as => .binary .pair a (tuple as)

def drop (n : Nat) (t : Term V) : Term V :=
  match n with
  | 0 => t
  | n + 1 => drop n (.unary .snd t)

/-- Zero-based indexing: `project i` is the source's π_(i+1). -/
def project (i : Nat) (t : Term V) : Term V := .unary .fst (drop i t)

end Term

variable {V : Type}

theorem EqE.drop {a b : Term V} (h : EqE a b) (n : Nat) :
    EqE (a.drop n) (b.drop n) := by
  induction n generalizing a b with
  | zero => exact h
  | succ n ih => exact ih (.unary .snd h)

theorem drop_tuple (xs : List (Term V)) :
    EqE ((Term.tuple xs).drop xs.length) (.const .bottom) := by
  induction xs with
  | nil => exact .refl _
  | cons a as ih =>
    exact ((EqE.equation (.snd a (Term.tuple as))).drop as.length).trans ih

theorem next_projection_tuple (xs : List (Term V)) :
    EqE ((Term.tuple xs).project xs.length) (.unary .fst (.const .bottom)) :=
  .unary .fst (drop_tuple xs)

/-- A separating interpretation disproves this equality, rather than just failing
 to find a rewrite. No equation of E constrains `fst(bottom)` to be `bottom`. -/
theorem fst_bottom_not_bottom :
    ¬ EqE (V := V) (.unary .fst (.const .bottom)) (.const .bottom) := by
  intro h
  have he := h.denote (fun _ => 0) (fun _ => 0)
  have hn : (Nat.unpair 2).1 ≠ 2 := Nat.ne_of_lt (Nat.unpair_lt (by decide))
  exact hn he

/-- The printed next-field guard fails on every canonical finite tuple. -/
theorem canonical_tuple_fails_printed_guard (xs : List (Term V)) :
    ¬ EqE ((Term.tuple xs).project xs.length) (.const .bottom) := by
  intro h
  exact fst_bottom_not_bottom ((next_projection_tuple xs).symm.trans h)

/-- A prefix may be followed by any term. This exposes the scope of the guard. -/
def tupleWithTail (xs : List (Term V)) (tail : Term V) : Term V :=
  xs.foldr (.binary .pair) tail

theorem drop_tupleWithTail (xs : List (Term V)) (tail : Term V) :
    EqE ((tupleWithTail xs tail).drop xs.length) tail := by
  induction xs with
  | nil => exact .refl _
  | cons a as ih =>
    exact ((EqE.equation (.snd a (tupleWithTail as tail))).drop as.length).trans ih

/-- Conversely the printed guard permits an extra bottom field and arbitrary tail. -/
theorem extra_bottom_passes_printed_guard (xs : List (Term V)) (tail : Term V) :
    EqE ((tupleWithTail xs (.binary .pair (.const .bottom) tail)).project xs.length)
      (.const .bottom) :=
  (EqE.unary .fst (drop_tupleWithTail xs (.binary .pair (.const .bottom) tail))).trans
    (.equation (.fst (.const .bottom) tail))

/-- The proposed tail check accepts the canonical encoding. This is only a
documented correction, not a privacy theorem for a modified protocol. -/
theorem canonical_tuple_passes_tail_guard (xs : List (Term V)) :
    EqE ((Term.tuple xs).drop xs.length) (.const .bottom) := drop_tuple xs

end ExplainableCrypto.Helios.Symbolic
