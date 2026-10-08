import Mathlib.Tactic

/-!
# A finite symbolic Helios attack experiment

See `docs/research/helios-model.md` for the source mapping and claim boundary.
Ciphertexts and proofs are ideal allocated handles, not ElGamal group elements.
Only the trusted tally reads the secret vote environment. Recipes receive public
ballots. This model establishes attack witnesses, not general ballot secrecy.
-/

namespace ExplainableCrypto.Helios

inductive Voter | alice | bob | mallory
  deriving DecidableEq, Repr

instance : Fintype Voter := ⟨{.alice, .bob, .mallory}, by intro value; cases value <;> simp⟩

inductive Vote | x | y | abstain
  deriving DecidableEq, Repr

instance : Fintype Vote := ⟨{.x, .y, .abstain}, by intro value; cases value <;> simp⟩

/-- Allocation names for opaque ciphertexts. `position = false` names the
original X component; no plaintext or cryptographic randomness is stored here. -/
structure Ciphertext where
  allocation : Voter
  position : Bool
  deriving DecidableEq, Repr

/-- An ideal certificate handle is associated with an issued ciphertext. -/
structure Component where
  ciphertext : Ciphertext
  proof : Ciphertext
  deriving DecidableEq, Repr

structure Ballot where
  x : Component
  y : Component
  /-- Certificate for the unordered pair issued at this allocation. -/
  aggregateProof : Voter
  deriving DecidableEq, Repr

def issued (who : Voter) : Ballot :=
  let x : Ciphertext := ⟨who, false⟩
  let y : Ciphertext := ⟨who, true⟩
  ⟨⟨x, x⟩, ⟨y, y⟩, who⟩

def Ballot.swap (b : Ballot) : Ballot := ⟨b.y, b.x, b.aggregateProof⟩

/-- Two-factor commutative-product equality for this allocated-atom fragment. -/
def sameAggregate (a b c d : Ciphertext) : Bool :=
  (a == c && b == d) || (a == d && b == c)

/-- Check certificate statements without reading the secret environment. -/
def valid (b : Ballot) : Bool :=
  b.x.proof == b.x.ciphertext && b.y.proof == b.y.ciphertext &&
    sameAggregate b.x.ciphertext b.y.ciphertext
      ⟨b.aggregateProof, false⟩ ⟨b.aggregateProof, true⟩

def sharesCiphertext (a b : Ballot) : Bool :=
  a.x.ciphertext == b.x.ciphertext || a.x.ciphertext == b.y.ciphertext ||
  a.y.ciphertext == b.x.ciphertext || a.y.ciphertext == b.y.ciphertext

inductive Policy | original | wholeBallot | components
  deriving DecidableEq, Repr

instance : Fintype Policy := ⟨{.original, .wholeBallot, .components}, by intro value; cases value <;> simp⟩

inductive Rejection | invalidProof | duplicateBallot | reusedCiphertext
  deriving DecidableEq, Repr

/-- Rejection terminates the finite run, rather than silently dropping a ballot
and tallying a smaller election. -/
def check (policy : Policy) (board : List Ballot) (b : Ballot) : Option Rejection :=
  if !valid b then some .invalidProof else
  match policy with
  | .original => none
  | .wholeBallot => if board.contains b then some .duplicateBallot else none
  | .components =>
    if board.any (sharesCiphertext b) then some .reusedCiphertext else none

structure PublicBoard where
  alice : Ballot
  bob : Ballot
  deriving DecidableEq, Repr

def publicBoard : PublicBoard := ⟨issued .alice, issued .bob⟩

/-- Finite adversary programs. Replay and permutation are permitted operations;
only the protocol policy decides whether to accept the resulting submission. -/
inductive Recipe
  | fresh (choice : Vote)
  | replay (targetBob : Bool)
  | permute (targetBob : Bool)
  | malformed
  deriving DecidableEq, Repr, Fintype

def Recipe.submit (r : Recipe) (board : PublicBoard) : Ballot :=
  match r with
  | .fresh _ => issued .mallory
  | .replay targetBob => if targetBob then board.bob else board.alice
  | .permute targetBob => (if targetBob then board.bob else board.alice).swap
  | .malformed => { issued .mallory with aggregateProof := .alice }

def Recipe.ownVote : Recipe → Vote
  | .fresh v => v
  | _ => .abstain

/-- Private state is only supplied to tallying, never to `Recipe.submit`. -/
abbrev Secrets := Voter → Vote

def secrets (swapped : Bool) (own : Vote) : Secrets
  | .alice => if swapped then .y else .x
  | .bob => if swapped then .x else .y
  | .mallory => own

def plaintext (s : Secrets) (c : Ciphertext) : Nat :=
  match s c.allocation, c.position with
  | .x, false | .y, true => 1
  | _, _ => 0

abbrev Tally := Nat × Nat

def tally (s : Secrets) (ballots : List Ballot) : Tally :=
  ballots.foldl (fun (x, y) b =>
    (x + plaintext s b.x.ciphertext, y + plaintext s b.y.ciphertext)) (0, 0)

inductive Outcome
  | rejected (reason : Rejection)
  | tallied (result : Tally)
  deriving DecidableEq, Repr

/-- Complete public observation of this finite experiment. It does not contain
the partial decryption/proof messages of the full cryptographic protocol. -/
structure View where
  board : PublicBoard
  submission : Ballot
  outcome : Outcome
  deriving DecidableEq, Repr

def run (policy : Policy) (swapped : Bool) (r : Recipe) : View :=
  let b := r.submit publicBoard
  let before := [publicBoard.alice, publicBoard.bob]
  let outcome := match check policy before b with
    | some reason => Outcome.rejected reason
    | none => Outcome.tallied (tally (secrets swapped r.ownVote) (before ++ [b]))
  ⟨publicBoard, b, outcome⟩

/-- A falsifiable property only for this finite recipe/observation model. -/
def RestrictedPrivacy (policy : Policy) : Prop :=
  ∀ r, run policy false r = run policy true r

/-- Public test; it has no input for secrets or the hidden world. -/
def xCountIs (n : Nat) (view : View) : Bool :=
  match view.outcome with
  | .tallied (x, _) => x == n
  | .rejected _ => false

end ExplainableCrypto.Helios
