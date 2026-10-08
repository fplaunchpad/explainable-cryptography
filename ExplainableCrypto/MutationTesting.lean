import Std

/-!
# Mutation testing for specifications

## Motivation

A proof that a program meets a specification does not show that the
specification expresses what its author intended. Mutation testing makes part
of that question concrete. We write down small, plausible alternatives called
*mutants*, then look for checked witnesses that expose the difference between
each mutant and the intended artifact.

Ordinary software mutation testing changes a program and asks whether a test
suite notices. This example applies the idea at two layers:

* A `Spec` says what it means for a construction to be acceptable.
* A **definition mutant** changes the `Spec`. Its witness is a construction that
  satisfies one definition and fails the other.
* A **construction mutant** changes the implementation while holding the
  definition fixed. Its witness is a concrete input on which the changed
  construction violates that definition.

The toy domain is intentionally elementary. A construction is a function
`Nat → Nat`, and the intended definition says that it must never decrease its
input. The original construction increments its input. This is not meant as a
security property in its own right; it gives the same logical shapes as the
cryptographic examples while keeping every proof readable without a library.

Every result below is checked by Lean. The mutants are enumerated manually, so
the demo illustrates classification and coverage rather than automatic mutant
generation or proof search.
-/

namespace ExplainableCrypto.MutationTesting

abbrev Scheme := Nat → Nat
abbrev Spec := Scheme → Prop

-- The pointwise requirement: at input `n` the output must be at least `n`.
-- Naming it lets the specification and the attack record below refer to the
-- same proposition rather than restating it.
def MeetsAt (f : Scheme) (n : Nat) : Prop := n ≤ f n

-- A specification is a predicate on constructions. The intended predicate
-- accepts exactly the functions that meet the requirement at every input.
def Intended : Spec := fun f => ∀ n, MeetsAt f n

-- These are depth-one mutants: each makes one local change to `Intended`.
--
-- * `Weaker` replaces the meaningful lower bound `n` by `0`. Every Nat-valued
--   function now passes, so this definition permits too much.
-- * `Stronger` raises the lower bound by one. It requires strict progress and
--   therefore rejects some functions accepted by `Intended`.
-- * `Equivalent` changes only notation: `f n ≥ n` means `n ≤ f n`.
def Weaker : Spec := fun f => ∀ n, 0 ≤ f n
def Stronger : Spec := fun f => ∀ n, n + 1 ≤ f n
def Equivalent : Spec := fun f => ∀ n, f n ≥ n

-- These functions play two roles below: candidate constructions to test
-- against mutated definitions, and mutations of the original `increment`.
def identity : Scheme := fun n => n
def zero : Scheme := fun _ => 0
def increment : Scheme := fun n => n + 1
def decrement : Scheme := fun n => n - 1

/-!
## Definition mutants

To classify one definition as *strictly weaker* than another, we need both:

1. an implication showing that everything accepted by the stronger definition
   is accepted by the weaker one; and
2. a separating construction accepted by the weaker definition but rejected
   by the stronger one.

The direction is reversed when classifying a strictly stronger mutant.
-/

-- Part 1 for the weaker mutant: every intended construction also satisfies the
-- mutant, because every natural number is at least zero.
theorem intended_implies_weaker : ∀ f, Intended f → Weaker f := by
  intro f _ n
  exact Nat.zero_le (f n)

-- Part 2: the constant-zero construction passes `Weaker`...
theorem zero_meets_weaker : Weaker zero := by
  intro n
  exact Nat.zero_le (zero n)

-- ...but fails `Intended` at input 1, where it would require 1 ≤ 0.
theorem zero_fails_intended : ¬ Intended zero := by
  intro h
  exact Nat.not_succ_le_zero 0 (h 1)

-- Package a separating construction together with proofs of both facts. This
-- structure is the definition-layer analogue of a test that kills a mutant.
structure Separates (left right : Spec) where
  scheme : Scheme
  left_holds : left scheme
  right_fails : ¬ right scheme

-- Together with `intended_implies_weaker`, this value certifies that `Weaker`
-- is strictly weaker, rather than merely different.
def weaker_separation : Separates Weaker Intended where
  scheme := zero
  left_holds := zero_meets_weaker
  right_fails := zero_fails_intended

-- Part 1 for the stronger mutant: raising the output by at least one certainly
-- implies not lowering it.
theorem stronger_implies_intended : ∀ f, Stronger f → Intended f := by
  intro f h n
  exact Nat.le_trans (Nat.le_succ n) (h n)

-- Part 2: identity is accepted by `Intended`...
theorem identity_meets_intended : Intended identity := by
  intro n
  exact Nat.le_refl n

-- ...but rejected by `Stronger`, already at input 0.
theorem identity_fails_stronger : ¬ Stronger identity := by
  intro h
  exact Nat.not_succ_le_zero 0 (h 0)

-- Together with `stronger_implies_intended`, this certifies that `Stronger` is
-- strictly stronger than the intended definition.
def stronger_separation : Separates Intended Stronger where
  scheme := identity
  left_holds := identity_meets_intended
  right_fails := identity_fails_stronger

-- Not every syntactic mutation changes meaning. Here both directions reduce to
-- the same proposition, so Lean discharges the mutant as equivalent.
theorem equivalent_iff_intended : ∀ f, Equivalent f ↔ Intended f := by
  intro f
  rfl

/-!
## Construction mutants

We now stop changing the definition. `Intended` remains the fixed acceptance
criterion, while we mutate the original `increment` construction.
-/

-- Establish the baseline: the unmutated construction meets the specification.
theorem increment_meets_intended : Intended increment := by
  intro n
  exact Nat.le_succ n

-- For this toy property, an attack is an input at which the construction
-- fails the pointwise requirement. The field is stated through `MeetsAt`, the
-- same proposition `Intended` quantifies over, so the record cannot drift from
-- the definition it refutes. In a cryptographic model this record would
-- instead contain an adversary and a proof that its advantage is
-- non-negligible.
structure Attack (f : Scheme) where
  input : Nat
  violates : ¬ MeetsAt f input

-- Mutating `increment` to always return zero is killed by input 1.
def zero_attack : Attack zero where
  input := 1
  violates := by simp [MeetsAt, zero]

-- Mutating it to decrement is also killed by input 1.
def decrement_attack : Attack decrement where
  input := 1
  violates := by simp [MeetsAt, decrement]

-- Any checked attack is sufficient to refute the universal specification. The
-- proof applies the alleged specification at the attack input and obtains the
-- exact proposition that the attack says is false.
theorem attack_refutes_intended {f : Scheme} (attack : Attack f) :
    ¬ Intended f := by
  intro h
  exact attack.violates (h attack.input)

-- These two mutants are therefore counted as killed, not merely suspected.
theorem zero_mutant_fails : ¬ Intended zero :=
  attack_refutes_intended zero_attack

theorem decrement_mutant_fails : ¬ Intended decrement :=
  attack_refutes_intended decrement_attack

-- Identity differs from increment, but `Intended` allows both. We must not call
-- this mutant insecure just because it changed: Lean proves that it preserves
-- this particular specification. That says nothing about other properties.
theorem identity_mutant_still_meets_spec : Intended identity :=
  identity_meets_intended

/-! ## Coverage report

Coverage asks how much of the chosen mutant space has a checked answer. It does
not count how many natural-number inputs were tried, and it does not claim that
the catalogue contains every possible mistake.

The lists below are an explicit inventory rather than an automated proof-search
engine. The theorems above justify every non-`unresolved` entry:

* `separated`: a construction distinguishes two definitions;
* `equivalent`: the mutated and intended definitions are proved equivalent;
* `killed`: a checked attack refutes a construction mutant;
* `preservesSpec`: the changed construction still satisfies the fixed spec;
* `unresolved`: neither a witness nor a preservation/equivalence proof was
  found. Failure to find an attack is not treated as evidence of security.
-/

inductive Status where
  | separated
  | equivalent
  | killed
  | preservesSpec
  | unresolved
  deriving Repr

def definitionResults : List (String × Status) :=
  [("weaker", .separated),
   ("stronger", .separated),
   ("equivalent", .equivalent)]

def constructionResults : List (String × Status) :=
  [("always zero", .killed),
   ("decrement", .killed),
   ("identity", .preservesSpec)]

#eval definitionResults
#eval constructionResults

-- In this small hand-built catalogue all six mutants are resolved: the
-- definition side has two separations and one equivalence, while the
-- construction side has two killed mutants and one specification-preserving
-- mutant. A realistic report would also retain and count unresolved entries.

end ExplainableCrypto.MutationTesting
