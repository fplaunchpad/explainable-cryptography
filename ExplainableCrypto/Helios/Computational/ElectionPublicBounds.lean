import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import ExplainableCrypto.Helios.Computational.ElectionOracle
import ExplainableCrypto.Helios.Computational.RepairedOutputStorage

/-! Structural widths of the actual public interaction records. These count all
scalar/group leaves, binary natural-number widths, and fixed/list overhead. They
are not asserted equal to the length of a particular nested bit codec. Uniform
scalar and fingerprint widths are explicit premises, independent of any group
representation assumption. No callback running-time bound is assumed here.

Enquiry: do the fixed three-voter source's public records have linear structural
width in their leaf widths? Falsifiers are an accepted fourth board entry, a
successful decoded value above the actual board length, or an omitted proof or
fingerprint field. The reality check is the original record definitions and the
two sequential honest submissions, followed by at most one attacker submission.
-/
namespace ExplainableCrypto.Helios.Computational.ElectionPublicBounds
open OracleComp
variable {F G : Type}

def ballotWidth (gwidth : G → Nat) (fwidth : F → Nat) (b : Ballot F G 2) : Nat :=
  1 + ((ballotGroupRecord b).map gwidth).sum + ((ballotScalarRecord b).map fwidth).sum

def boardWidth (gwidth : G → Nat) (fwidth : F → Nat) (board : List (BoardEntry F G)) : Nat :=
  1 + (board.map (fun e => ballotWidth gwidth fwidth e.ballot + 3)).sum

def parametersWidth (gwidth : G → Nat) (fwidth : F → Nat) (p : PublicParameters F G) : Nat :=
  1 + gwidth p.generator + gwidth p.publicKey + gwidth p.trusteeKeyProof.commitment +
    fwidth p.trusteeKeyProof.response + (p.candidates.map (fun n => n.size + 1)).sum +
    3 * p.eligibleVoters.length

def prefixWidth (gwidth : G → Nat) (fwidth : F → Nat) (p : PublicPrefix F G) : Nat :=
  1 + parametersWidth gwidth fwidth p.parameters + p.fingerprint.size + 1 + 4 +
    boardWidth gwidth fwidth p.board

def decodedWidth : Option Nat → Nat
  | none => 1
  | some n => 1 + n.size

def resultWidth (gwidth : G → Nat) (fwidth : F → Nat) (r : PublicResult F G) : Nat :=
  1 + prefixWidth gwidth fwidth r.beforeTally + ballotWidth gwidth fwidth r.submission + 2 +
    boardWidth gwidth fwidth r.board +
    (List.ofFn (fun i : Fin 2 => gwidth (r.encryptedTally i).1 + gwidth (r.encryptedTally i).2 +
      gwidth (r.decryptionShares i) + gwidth (r.decryptionProofs i).commitment.1 +
      gwidth (r.decryptionProofs i).commitment.2 + fwidth (r.decryptionProofs i).response +
      decodedWidth (r.decodedTally i))).sum

def prefixBound (W : Nat) := 100 * (W + 1)
def resultBound (W B : Nat) := B + 1000 * (W + 1)

private theorem sum_width_le {A : Type} (width : A → Nat) (xs : List A) (W : Nat)
    (h : ∀ x ∈ xs, width x ≤ W) : (xs.map width).sum ≤ xs.length * W := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem ballot_width_le (gwidth : G → Nat) (fwidth : F → Nat) (W : Nat)
    (hg : ∀ g, gwidth g ≤ W) (hf : ∀ f, fwidth f ≤ W) (b : Ballot F G 2) :
    ballotWidth gwidth fwidth b ≤ 28 * W + 1 := by
  have h1 := sum_width_le gwidth (ballotGroupRecord b) W (fun g _ => hg g)
  have h2 := sum_width_le fwidth (ballotScalarRecord b) W (fun f _ => hf f)
  rw [ballotGroupRecord_length] at h1
  rw [ballotScalarRecord_length] at h2
  unfold ballotWidth
  omega

theorem board_width_le (gwidth : G → Nat) (fwidth : F → Nat) (W : Nat)
    (hg : ∀ g, gwidth g ≤ W) (hf : ∀ f, fwidth f ≤ W) (board : List (BoardEntry F G)) :
    boardWidth gwidth fwidth board ≤ 1 + board.length * (28 * W + 4) := by
  have h := sum_width_le (fun e : BoardEntry F G => ballotWidth gwidth fwidth e.ballot + 3)
    board (28*W+4) (fun e _ => by have := ballot_width_le gwidth fwidth W hg hf e.ballot; omega)
  unfold boardWidth
  omega

theorem prefix_width_le (gwidth : G → Nat) (fwidth : F → Nat) (W : Nat)
    (hg : ∀ g, gwidth g ≤ W) (hf : ∀ f, fwidth f ≤ W) (before : PublicPrefix F G)
    (hfp : before.fingerprint.size ≤ W)
    (hc : before.parameters.candidates = [0,1])
    (he : before.parameters.eligibleVoters = [0,1,2])
    (hb : before.board.length ≤ 2) : prefixWidth gwidth fwidth before ≤ prefixBound W := by
  have hboard := board_width_le gwidth fwidth W hg hf before.board
  have hboard' := Nat.mul_le_mul_right (28*W+4) hb
  have h0 := hg before.parameters.generator
  have h1 := hg before.parameters.publicKey
  have h2 := hg before.parameters.trusteeKeyProof.commitment
  have h3 := hf before.parameters.trusteeKeyProof.response
  simp only [prefixWidth,parametersWidth,hc,he,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,List.length_cons,List.length_nil]
  norm_num [prefixBound]
  omega

private theorem decoded_width_le (d : Option Nat) (h : ∀ n, d = some n → n ≤ 3) :
    decodedWidth d ≤ 3 := by
  cases d with
  | none => decide
  | some n =>
    have hn := h n rfl
    have hs : n.size ≤ 2 := Nat.size_le_size hn
    change 1 + n.size ≤ 3
    omega

theorem result_width_le (gwidth : G → Nat) (fwidth : F → Nat) (W B : Nat)
    (hg : ∀ g, gwidth g ≤ W) (hf : ∀ f, fwidth f ≤ W) (view : PublicResult F G)
    (hp : prefixWidth gwidth fwidth view.beforeTally ≤ B)
    (hb : view.board.length ≤ 3)
    (hd : ∀ i n, view.decodedTally i = some n → n ≤ 3) :
    resultWidth gwidth fwidth view ≤ resultBound W B := by
  have hballot := ballot_width_le gwidth fwidth W hg hf view.submission
  have hboard := board_width_le gwidth fwidth W hg hf view.board
  have hboard' := Nat.mul_le_mul_right (28*W+4) hb
  have hsum := sum_width_le
    (fun i : Fin 2 => gwidth (view.encryptedTally i).1 + gwidth (view.encryptedTally i).2 +
      gwidth (view.decryptionShares i) + gwidth (view.decryptionProofs i).commitment.1 +
      gwidth (view.decryptionProofs i).commitment.2 + fwidth (view.decryptionProofs i).response +
      decodedWidth (view.decodedTally i)) [0,1] (6*W+3) (by
        intro i _
        have h0 := hg (view.encryptedTally i).1
        have h1 := hg (view.encryptedTally i).2
        have h2 := hg (view.decryptionShares i)
        have h3 := hg (view.decryptionProofs i).commitment.1
        have h4 := hg (view.decryptionProofs i).commitment.2
        have h5 := hf (view.decryptionProofs i).response
        have h6 := decoded_width_le (view.decodedTally i) (hd i)
        omega)
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,
    List.length_nil] at hsum
  simp only [resultWidth,List.ofFn_succ,List.ofFn_zero,List.sum_cons,List.sum_nil,
    Fin.succ_zero_eq_one]
  unfold resultBound
  omega

section Source
variable [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

private theorem lifted_submit_length (g pk : G) (voter : Fin 3)
    (board : List (BoardEntry F G)) (b : Ballot F G 2)
    (out : Decision × List (BoardEntry F G))
    (ho : out ∈ support (ElectionOracle.liftBallot (repairedSubmitOracle g pk voter board b))) :
    out.2.length ≤ board.length + 1 := by
  simp only [ElectionOracle.liftBallot,repairedSubmitOracle,simulateQ_bind,
    mem_support_bind_iff] at ho
  obtain ⟨valid,_,ho⟩ := ho
  split at ho
  · split at ho
    · simp only [simulateQ_pure,mem_support_pure_iff] at ho
      subst out
      simp
    · simp only [simulateQ_pure,mem_support_pure_iff] at ho
      subst out
      exact Nat.le_add_right _ _
  · simp only [simulateQ_pure,mem_support_pure_iff] at ho
    subst out
    exact Nat.le_add_right _ _

private theorem lifted_pair_length (g pk : G) (vote : Bool) (alice bob : HonestCoins F)
    (out : (Decision × Decision) × List (BoardEntry F G))
    (ho : out ∈ support (ElectionOracle.liftBallot
      (repairedCastHonestPairWithCoinsOracle g pk vote alice bob))) : out.2.length ≤ 2 := by
  simp only [ElectionOracle.liftBallot,repairedCastHonestPairWithCoinsOracle,simulateQ_bind,
    simulateQ_pure,mem_support_bind_iff,mem_support_pure_iff] at ho
  obtain ⟨a,_,first,hfirst,b,_,second,hsecond,rfl⟩ := ho
  have h1 := lifted_submit_length g pk 0 [] a first hfirst
  have h2 := lifted_submit_length g pk 1 first.2 b second hsecond
  simp only [List.length_nil] at h1
  change second.2.length ≤ 2
  omega

/-- Every possible oracle answer is allowed: no verification or collision
hypothesis is needed for the actual prefix's list and fingerprint shape. -/
theorem support_prefix_shape (fingerprint : PublicParameters F G → Nat) (g : G)
    (secret keyNonce : F) (vote : Bool) (alice bob : HonestCoins F) (before : PublicPrefix F G)
    (ho : before ∈ support (ElectionOracle.prefixWithCoins fingerprint g secret keyNonce vote alice bob)) :
    before.parameters.candidates = [0,1] ∧ before.parameters.eligibleVoters = [0,1,2] ∧
      before.fingerprint = fingerprint before.parameters ∧ before.board.length ≤ 2 := by
  simp only [ElectionOracle.prefixWithCoins,mem_support_bind_iff,mem_support_pure_iff] at ho
  obtain ⟨keyProof,_,cast,hcast,rfl⟩ := ho
  exact ⟨rfl,rfl,rfl,lifted_pair_length g (secret • g) vote alice bob cast hcast⟩

theorem support_prefix_width (gwidth : G → Nat) (fwidth : F → Nat) (W : Nat)
    (hg : ∀ g, gwidth g ≤ W) (hf : ∀ f, fwidth f ≤ W)
    (fingerprint : PublicParameters F G → Nat)
    (hfp : ∀ p : PublicParameters F G, p.candidates = [0,1] →
      p.eligibleVoters = [0,1,2] → (fingerprint p).size ≤ W)
    (g : G) (secret keyNonce : F) (vote : Bool) (alice bob : HonestCoins F)
    (before : PublicPrefix F G)
    (ho : before ∈ support (ElectionOracle.prefixWithCoins fingerprint g secret keyNonce vote alice bob)) :
    prefixWidth gwidth fwidth before ≤ prefixBound W ∧ before.board.length ≤ 2 := by
  obtain ⟨hc,he,hfinger,hb⟩ := support_prefix_shape fingerprint g secret keyNonce vote alice bob before ho
  exact ⟨prefix_width_le gwidth fwidth W hg hf before (hfinger ▸ hfp before.parameters hc he) hc he hb,hb⟩

omit [DecidableEq F] in
theorem decodeBounded_le (g : G) (bound : Nat) (message : G) (n : Nat)
    (h : decodeBounded (F := F) g bound message = some n) : n ≤ bound := by
  have hn : n ∈ List.range (bound+1) := List.mem_of_find?_eq_some h
  have := List.mem_range.mp hn
  omega

/-- Arbitrary submissions and every rejection path keep at most one new entry.
Successful decoding is bounded by the actual final board, not by field size. -/
theorem support_finish_shape (secret : F) (nonces : Fin 2 → F) (before : PublicPrefix F G)
    (submission : Ballot F G 2) (view : PublicResult F G)
    (ho : view ∈ support (ElectionOracle.finishWithCoins secret nonces before submission)) :
    view.beforeTally = before ∧ view.board.length ≤ before.board.length + 1 ∧
      (∀ i n, view.decodedTally i = some n → n ≤ view.board.length) := by
  simp only [ElectionOracle.finishWithCoins,mem_support_bind_iff,mem_support_pure_iff] at ho
  obtain ⟨cast,hcast,proof0,_,proof1,_,rfl⟩ := ho
  exact ⟨rfl,lifted_submit_length _ _ _ _ _ cast hcast,
    fun i n hn => decodeBounded_le _ _ _ n hn⟩

theorem finish_width_le (gwidth : G → Nat) (fwidth : F → Nat) (W B : Nat)
    (hg : ∀ g, gwidth g ≤ W) (hf : ∀ f, fwidth f ≤ W)
    (secret : F) (nonces : Fin 2 → F) (before : PublicPrefix F G)
    (hp : prefixWidth gwidth fwidth before ≤ B) (hb : before.board.length ≤ 2)
    (submission : Ballot F G 2) (view : PublicResult F G)
    (ho : view ∈ support (ElectionOracle.finishWithCoins secret nonces before submission)) :
    resultWidth gwidth fwidth view ≤ resultBound W B ∧ view.board.length ≤ 3 ∧
      (∀ i n, view.decodedTally i = some n → n ≤ 3) := by
  obtain ⟨hbefore,hboard,hd⟩ := support_finish_shape secret nonces before submission view ho
  have h3 : view.board.length ≤ 3 := by omega
  have hdec : ∀ i n, view.decodedTally i = some n → n ≤ 3 :=
    fun i n hn => (hd i n hn).trans h3
  exact ⟨result_width_le gwidth fwidth W B hg hf view (hbefore ▸ hp) h3 hdec,h3,hdec⟩
end Source

/-- Scalar widths require their own envelope; a group encoding bound does not
supply this binary modulus bound. -/
theorem scalar_width_le (q : Nat) [NeZero q] (x : ZMod q) : x.val.size ≤ q.size :=
  Nat.size_le_size (Nat.le_of_lt x.val_lt)

namespace Controls
private def ballot : Ballot Unit Unit 2 :=
  ⟨fun _ => ((),()), fun _ => ⟨⟨(),(),(),()⟩,⟨(),(),(),()⟩⟩,⟨⟨(),(),(),()⟩,⟨(),(),(),()⟩⟩⟩
private def samplePrefix (fingerprint : Nat) : PublicPrefix Unit Unit :=
  ⟨⟨(),(),⟨(),()⟩,[0,1],[0,1,2]⟩,fingerprint,(.accepted,.accepted),[⟨0,ballot⟩,⟨1,ballot⟩]⟩

/-- Independently counted: sixteen group leaves, twelve scalar leaves, one
ballot-record overhead. These are structural controls, not execution traces. -/
theorem full_ballot : ballotWidth (fun _ : Unit => 1) (fun _ : Unit => 1) ballot = 29 := rfl

theorem omitted_proof_rejected : ballotWidth (fun _ : Unit => 1) (fun _ : Unit => 1) ballot ≠ 17 := by
  decide

theorem prefix_literal : prefixWidth (fun _ : Unit => 1) (fun _ : Unit => 1) (samplePrefix 0) = 88 := rfl

theorem fingerprint_retained : prefixWidth (fun _ : Unit => 1) (fun _ : Unit => 1) (samplePrefix 8) = 92 := rfl

theorem fingerprint_omission_rejected :
    prefixWidth (fun _ : Unit => 1) (fun _ : Unit => 1) (samplePrefix 8) ≠
      prefixWidth (fun _ : Unit => 1) (fun _ : Unit => 1) (samplePrefix 0) := by decide

theorem decode_boundary : decodedWidth (some 3) = 3 := rfl

theorem missing_not_zero : decodedWidth none = 1 ∧ (none : Option Nat) ≠ some 0 := by decide
end Controls

#print axioms support_prefix_width
#print axioms finish_width_le
end ExplainableCrypto.Helios.Computational.ElectionPublicBounds
