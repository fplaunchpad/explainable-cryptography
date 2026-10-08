import ExplainableCrypto.Helios.Computational.ElectionPublicBounds
import ExplainableCrypto.Helios.Computational.PublicObservationCodec

/-! The existing complete public-record framing with supplied leaf encoders.
These definitions specialize definitionally to the existing prime-group public
codecs. The length bounds charge every nested length/count prefix. They do not
assert a running-time bound for an encoder or for an attacker callback. -/
namespace ExplainableCrypto.Helios.Computational.ElectionPublicEncoding
open ElectionPublicBounds
variable {F G : Type}

private def pair (a b : List Bool) := bitFieldsEncode [a,b]
private def two {A : Type} (encode : A → List Bool) (v : Fin 2 → A) := pair (encode (v 0)) (encode (v 1))
private def list {A : Type} (encode : A → List Bool) (v : List A) := bitFieldsEncode (v.map encode)
private def cipher (ge : G → List Bool) (v : Ciphertext G) := pair (ge v.1) (ge v.2)
private def branch (ge : G → List Bool) (fe : F → List Bool) (v : Branch F G) :=
  pair (cipher ge (v.a,v.b)) (pair (fe v.challenge) (fe v.response))
private def proof (ge : G → List Bool) (fe : F → List Bool) (v : Proof01 F G) :=
  pair (branch ge fe v.zero) (branch ge fe v.one)
private def ballot (ge : G → List Bool) (fe : F → List Bool) (v : Ballot F G 2) :=
  pair (two (cipher ge) v.ciphertext) (pair (two (proof ge fe) v.proof) (proof ge fe v.overall))
private def board (ge : G → List Bool) (fe : F → List Bool) (v : List (BoardEntry F G)) :=
  list (fun e => pair (ballotVoterBitCodec.encode e.voter) (ballot ge fe e.ballot)) v
private def schnorr {A : Type} (ae : A → List Bool) (fe : F → List Bool) (v : SchnorrProof F A) :=
  pair (ae v.commitment) (fe v.response)
private def parameters (ge : G → List Bool) (fe : F → List Bool) (v : PublicParameters F G) :=
  pair (cipher ge (v.generator,v.publicKey))
    (pair (schnorr ge fe v.trusteeKeyProof)
      (pair (list ballotNatBitCodec.encode v.candidates) (list ballotVoterBitCodec.encode v.eligibleVoters)))

def encodePrefix (ge : G → List Bool) (fe : F → List Bool) (v : PublicPrefix F G) :=
  pair (parameters ge fe v.parameters) (pair (ballotNatBitCodec.encode v.fingerprint)
    (pair (pair (ballotDecisionBitCodec.encode v.honestDecisions.1)
      (ballotDecisionBitCodec.encode v.honestDecisions.2)) (board ge fe v.board)))

def encodeResult (ge : G → List Bool) (fe : F → List Bool) (v : PublicResult F G) :=
  pair (encodePrefix ge fe v.beforeTally) (pair (ballot ge fe v.submission)
    (pair (ballotDecisionBitCodec.encode v.decision) (pair (board ge fe v.board)
      (pair (two (cipher ge) v.encryptedTally) (pair (two ge v.decryptionShares)
        (pair (two (schnorr (cipher ge) fe) v.decryptionProofs)
          (two ballotDecodedBitCodec.encode v.decodedTally)))))))

theorem prime_prefix_eq {p q : Nat} [NeZero p] [NeZero q]
    (v : PublicPrefix (ZMod q) (PrimeGroup p q)) :
    encodePrefix (primeGroupBitCodec p q).encode (primeScalarBitCodec q).encode v =
      (ballotPublicPrefixBitCodec p q).encode v := rfl

theorem prime_result_eq {p q : Nat} [NeZero p] [NeZero q]
    (v : PublicResult (ZMod q) (PrimeGroup p q)) :
    encodeResult (primeGroupBitCodec p q).encode (primeScalarBitCodec q).encode v =
      (ballotPublicResultBitCodec p q).encode v := rfl

private theorem size_self (n : Nat) : n.size ≤ n := Nat.size_le.mpr n.lt_two_pow_self

private theorem pair_length (a b : List Bool) : (pair a b).length ≤ 7 + 3*a.length + 3*b.length := by
  have ha := size_self a.length
  have hb := size_self b.length
  rw [pair,bitFieldsEncode_length]
  simp only [List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,Nat.add_zero,show (2 : Nat).size = 2 from rfl]
  omega

private theorem list_length {A : Type} (enc : A → List Bool) (xs : List A) :
    (list enc xs).length ≤ 1 + 3*(xs.map (fun x => (enc x).length + 1)).sum := by
  have hs : (xs.map (fun x => 2*(enc x).length.size+1+(enc x).length)).sum + 2*xs.length ≤
      3*(xs.map (fun x => (enc x).length+1)).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hx := size_self (enc x).length
      simp only [List.map_cons,List.sum_cons,List.length_cons] at *
      omega
  have hc := size_self xs.length
  rw [list,bitFieldsEncode_length]
  simp only [List.length_map,List.map_map,Function.comp_def]
  omega

private theorem sum_mono {A : Type} (a b : A → Nat) (xs : List A) (h : ∀ x ∈ xs, a x ≤ b x) :
    (xs.map a).sum ≤ (xs.map b).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons]
    omega

private theorem sum_mul {A : Type} (w : A → Nat) (xs : List A) (C : Nat) :
    (xs.map (fun x => C * w x)).sum = C * (xs.map w).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.mul_add]

private theorem ballot_length (ge : G → List Bool) (fe : F → List Bool) (v : Ballot F G 2) :
    (ballot ge fe v).length ≤ 100000 * ballotWidth (fun g => (ge g).length) (fun f => (fe f).length) v := by
  have hb (v : Branch F G) : (branch ge fe v).length ≤
      49 + 9*((ge v.a).length+(ge v.b).length+(fe v.challenge).length+(fe v.response).length) := by
    have h0 := pair_length (ge v.a) (ge v.b)
    have h1 := pair_length (fe v.challenge) (fe v.response)
    have h2 := pair_length (cipher ge (v.a,v.b)) (pair (fe v.challenge) (fe v.response))
    change (pair (ge v.a) (ge v.b)).length ≤ _ at h0
    change (cipher ge (v.a,v.b)).length ≤ _ at h0
    change (pair (cipher ge (v.a,v.b)) (pair (fe v.challenge) (fe v.response))).length ≤ _
    omega
  have hp (v : Proof01 F G) := pair_length (branch ge fe v.zero) (branch ge fe v.one)
  have hc (i : Fin 2) := pair_length (ge (v.ciphertext i).1) (ge (v.ciphertext i).2)
  have hct := pair_length (cipher ge (v.ciphertext 0)) (cipher ge (v.ciphertext 1))
  have hpr := pair_length (proof ge fe (v.proof 0)) (proof ge fe (v.proof 1))
  have hpo := pair_length (two (proof ge fe) v.proof) (proof ge fe v.overall)
  have hall := pair_length (two (cipher ge) v.ciphertext)
    (pair (two (proof ge fe) v.proof) (proof ge fe v.overall))
  have hb0 := hb (v.proof 0).zero
  have hb1 := hb (v.proof 0).one
  have hb2 := hb (v.proof 1).zero
  have hb3 := hb (v.proof 1).one
  have hb4 := hb v.overall.zero
  have hb5 := hb v.overall.one
  have hp0 := hp (v.proof 0)
  have hp1 := hp (v.proof 1)
  have hp2 := hp v.overall
  have hc0 := hc 0
  have hc1 := hc 1
  simp only [ballot,proof,two,cipher,ballotWidth,ballotGroupRecord,ballotScalarRecord,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at *
  omega

private theorem voter_length (v : Fin 3) : (ballotVoterBitCodec.encode v).length ≤ 5 := by
  fin_cases v <;> decide

private theorem decision_length (v : Decision) : (ballotDecisionBitCodec.encode v).length = 2 := by
  cases v <;> rfl

private theorem board_length (ge : G → List Bool) (fe : F → List Bool) (v : List (BoardEntry F G)) :
    (board ge fe v).length ≤ 1000000 * boardWidth (fun g => (ge g).length) (fun f => (fe f).length) v := by
  have hl := list_length (fun e : BoardEntry F G => pair (ballotVoterBitCodec.encode e.voter)
    (ballot ge fe e.ballot)) v
  have hs := sum_mono (fun e : BoardEntry F G =>
    (pair (ballotVoterBitCodec.encode e.voter) (ballot ge fe e.ballot)).length+1)
    (fun e => 300001*(ballotWidth (fun g => (ge g).length) (fun f => (fe f).length) e.ballot+3)) v (by
      intro e _
      have hv := voter_length e.voter
      have hb := ballot_length ge fe e.ballot
      have hp := pair_length (ballotVoterBitCodec.encode e.voter) (ballot ge fe e.ballot)
      omega)
  rw [sum_mul] at hs
  unfold board boardWidth
  omega

private theorem parameters_length (ge : G → List Bool) (fe : F → List Bool) (v : PublicParameters F G) :
    (parameters ge fe v).length ≤ 10000 * parametersWidth (fun g => (ge g).length) (fun f => (fe f).length) v := by
  have hnc := list_length ballotNatBitCodec.encode v.candidates
  have hnv := list_length ballotVoterBitCodec.encode v.eligibleVoters
  have hns := sum_mono (fun n => (ballotNatBitCodec.encode n).length+1)
    (fun n => 2*(n.size+1)) v.candidates (by intro n _; simp only [ballotNatBitCodec,uniformNatEncode_length]; omega)
  rw [sum_mul] at hns
  have hvs := sum_mono (fun v => (ballotVoterBitCodec.encode v).length+1)
    (fun _ => 6) v.eligibleVoters (by intro v _; have := voter_length v; omega)
  simp only [List.map_const',List.sum_replicate,nsmul_eq_mul,Nat.cast_id] at hvs
  have h0 := pair_length (ge v.generator) (ge v.publicKey)
  have h1 := pair_length (ge v.trusteeKeyProof.commitment) (fe v.trusteeKeyProof.response)
  have h2 := pair_length (list ballotNatBitCodec.encode v.candidates)
    (list ballotVoterBitCodec.encode v.eligibleVoters)
  have h3 := pair_length (schnorr ge fe v.trusteeKeyProof)
    (pair (list ballotNatBitCodec.encode v.candidates) (list ballotVoterBitCodec.encode v.eligibleVoters))
  have h4 := pair_length (cipher ge (v.generator,v.publicKey))
    (pair (schnorr ge fe v.trusteeKeyProof)
      (pair (list ballotNatBitCodec.encode v.candidates) (list ballotVoterBitCodec.encode v.eligibleVoters)))
  simp only [parameters,parametersWidth,cipher,schnorr] at *
  omega

/-- A fixed factor for all records, including arbitrarily long candidate/board
lists. The source shape theorem separately gives the small reached bound. -/
theorem prefix_length_le (ge : G → List Bool) (fe : F → List Bool) (v : PublicPrefix F G) :
    (encodePrefix ge fe v).length ≤
      100000000 * prefixWidth (fun g => (ge g).length) (fun f => (fe f).length) v := by
  have hp := parameters_length ge fe v.parameters
  have hb := board_length ge fe v.board
  have hd0 := decision_length v.honestDecisions.1
  have hd1 := decision_length v.honestDecisions.2
  have hn : (ballotNatBitCodec.encode v.fingerprint).length = 2*v.fingerprint.size+1 := uniformNatEncode_length _
  have h0 := pair_length (ballotDecisionBitCodec.encode v.honestDecisions.1)
    (ballotDecisionBitCodec.encode v.honestDecisions.2)
  have h1 := pair_length (pair (ballotDecisionBitCodec.encode v.honestDecisions.1)
    (ballotDecisionBitCodec.encode v.honestDecisions.2)) (board ge fe v.board)
  have h2 := pair_length (ballotNatBitCodec.encode v.fingerprint)
    (pair (pair (ballotDecisionBitCodec.encode v.honestDecisions.1)
      (ballotDecisionBitCodec.encode v.honestDecisions.2)) (board ge fe v.board))
  have h3 := pair_length (parameters ge fe v.parameters) (pair (ballotNatBitCodec.encode v.fingerprint)
    (pair (pair (ballotDecisionBitCodec.encode v.honestDecisions.1)
      (ballotDecisionBitCodec.encode v.honestDecisions.2)) (board ge fe v.board)))
  unfold encodePrefix prefixWidth
  omega

private theorem decoded_length (v : Option Nat) : (ballotDecodedBitCodec.encode v).length ≤ 2*decodedWidth v := by
  cases v with
  | none => decide
  | some n => simp [ballotDecodedBitCodec,ballotNatBitCodec,decodedWidth,uniformNatEncode_length]; omega

/-- Full-result bound includes both boards, the complete submission, all
trustee proofs and both Option tags and decoded naturals. -/
theorem result_length_le (ge : G → List Bool) (fe : F → List Bool) (v : PublicResult F G) :
    (encodeResult ge fe v).length ≤
      10000000000 * resultWidth (fun g => (ge g).length) (fun f => (fe f).length) v := by
  have hp := prefix_length_le ge fe v.beforeTally
  have hballot := ballot_length ge fe v.submission
  have hd := decision_length v.decision
  have hboard := board_length ge fe v.board
  have hc (i : Fin 2) := pair_length (ge (v.encryptedTally i).1) (ge (v.encryptedTally i).2)
  have hs (i : Fin 2) := pair_length (ge (v.decryptionProofs i).commitment.1)
    (ge (v.decryptionProofs i).commitment.2)
  have hpr (i : Fin 2) := pair_length (cipher ge (v.decryptionProofs i).commitment) (fe (v.decryptionProofs i).response)
  have hct := pair_length (cipher ge (v.encryptedTally 0)) (cipher ge (v.encryptedTally 1))
  have hshare := pair_length (ge (v.decryptionShares 0)) (ge (v.decryptionShares 1))
  have hproof := pair_length (schnorr (cipher ge) fe (v.decryptionProofs 0)) (schnorr (cipher ge) fe (v.decryptionProofs 1))
  have hdecode := pair_length (ballotDecodedBitCodec.encode (v.decodedTally 0)) (ballotDecodedBitCodec.encode (v.decodedTally 1))
  have h0 := decoded_length (v.decodedTally 0)
  have h1 := decoded_length (v.decodedTally 1)
  have hc0 := hc 0
  have hc1 := hc 1
  have hs0 := hs 0
  have hs1 := hs 1
  have hpr0 := hpr 0
  have hpr1 := hpr 1
  have h2 := pair_length (two (schnorr (cipher ge) fe) v.decryptionProofs) (two ballotDecodedBitCodec.encode v.decodedTally)
  have h3 := pair_length (two ge v.decryptionShares)
    (pair (two (schnorr (cipher ge) fe) v.decryptionProofs) (two ballotDecodedBitCodec.encode v.decodedTally))
  have h4 := pair_length (two (cipher ge) v.encryptedTally) (pair (two ge v.decryptionShares)
    (pair (two (schnorr (cipher ge) fe) v.decryptionProofs) (two ballotDecodedBitCodec.encode v.decodedTally)))
  have h5 := pair_length (board ge fe v.board) (pair (two (cipher ge) v.encryptedTally) (pair (two ge v.decryptionShares)
    (pair (two (schnorr (cipher ge) fe) v.decryptionProofs) (two ballotDecodedBitCodec.encode v.decodedTally))))
  have h6 := pair_length (ballotDecisionBitCodec.encode v.decision) (pair (board ge fe v.board)
    (pair (two (cipher ge) v.encryptedTally) (pair (two ge v.decryptionShares)
      (pair (two (schnorr (cipher ge) fe) v.decryptionProofs) (two ballotDecodedBitCodec.encode v.decodedTally)))))
  have h7 := pair_length (ballot ge fe v.submission) (pair (ballotDecisionBitCodec.encode v.decision) (pair (board ge fe v.board)
    (pair (two (cipher ge) v.encryptedTally) (pair (two ge v.decryptionShares)
      (pair (two (schnorr (cipher ge) fe) v.decryptionProofs) (two ballotDecodedBitCodec.encode v.decodedTally))))))
  have h8 := pair_length (encodePrefix ge fe v.beforeTally) (pair (ballot ge fe v.submission)
    (pair (ballotDecisionBitCodec.encode v.decision) (pair (board ge fe v.board)
      (pair (two (cipher ge) v.encryptedTally) (pair (two ge v.decryptionShares)
        (pair (two (schnorr (cipher ge) fe) v.decryptionProofs) (two ballotDecodedBitCodec.encode v.decodedTally)))))))
  simp only [encodeResult,resultWidth,two,cipher,schnorr,List.ofFn_succ,List.ofFn_zero,
    List.sum_cons,List.sum_nil,Fin.succ_zero_eq_one] at *
  omega

private theorem fields_injective : Function.Injective bitFieldsEncode := by
  intro x y h
  have he := congrArg bitFieldsDecode h
  simpa only [bitFieldsDecode_encode,Option.some.injEq] using he

private theorem pair_eq_iff (a b c d : List Bool) : pair a b = pair c d ↔ a = c ∧ b = d := by
  simpa only [pair,List.cons.injEq,and_true] using
    (fields_injective.eq_iff (a := [a,b]) (b := [c,d]))

private theorem list_injective {A : Type} {enc : A → List Bool} (h : Function.Injective enc) :
    Function.Injective (list enc) := by
  intro x y he
  have hm := fields_injective he
  exact List.map_injective_iff.mpr h hm

private theorem two_injective {A : Type} {enc : A → List Bool} (h : Function.Injective enc) :
    Function.Injective (two enc) := by
  intro x y he
  obtain ⟨h0,h1⟩ := (pair_eq_iff _ _ _ _).mp he
  funext i
  fin_cases i
  · exact h h0
  · exact h h1

private theorem cipher_injective {ge : G → List Bool} (hg : Function.Injective ge) :
    Function.Injective (cipher ge) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  obtain ⟨h0,h1⟩ := (pair_eq_iff _ _ _ _).mp h
  exact Prod.ext (hg h0) (hg h1)

private theorem branch_injective {ge : G → List Bool} {fe : F → List Bool}
    (hg : Function.Injective ge) (hf : Function.Injective fe) : Function.Injective (branch ge fe) := by
  rintro ⟨a,b,c,d⟩ ⟨e,f,g,h⟩ he
  simp only [branch,cipher,pair_eq_iff,hg.eq_iff,hf.eq_iff] at he
  rcases he with ⟨⟨rfl,rfl⟩,rfl,rfl⟩
  rfl

private theorem proof_injective {ge : G → List Bool} {fe : F → List Bool}
    (hg : Function.Injective ge) (hf : Function.Injective fe) : Function.Injective (proof ge fe) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ he
  simp only [proof,pair_eq_iff,(branch_injective hg hf).eq_iff] at he
  rcases he with ⟨rfl,rfl⟩
  rfl

private theorem ballot_injective {ge : G → List Bool} {fe : F → List Bool}
    (hg : Function.Injective ge) (hf : Function.Injective fe) : Function.Injective (ballot ge fe) := by
  rintro ⟨a,b,c⟩ ⟨d,e,f⟩ he
  simp only [ballot,pair_eq_iff,(two_injective (cipher_injective hg)).eq_iff,
    (two_injective (proof_injective hg hf)).eq_iff,(proof_injective hg hf).eq_iff] at he
  rcases he with ⟨rfl,rfl,rfl⟩
  rfl

private theorem board_injective {ge : G → List Bool} {fe : F → List Bool}
    (hg : Function.Injective ge) (hf : Function.Injective fe) : Function.Injective (board ge fe) := by
  apply list_injective
  rintro ⟨a,b⟩ ⟨c,d⟩ he
  simp only [pair_eq_iff,(BitRecordCodec.injective ballotVoterBitCodec).eq_iff,
    (ballot_injective hg hf).eq_iff] at he
  rcases he with ⟨rfl,rfl⟩
  rfl

private theorem schnorr_injective {A : Type} {ae : A → List Bool} {fe : F → List Bool}
    (ha : Function.Injective ae) (hf : Function.Injective fe) : Function.Injective (schnorr ae fe) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ he
  simp only [schnorr,pair_eq_iff,ha.eq_iff,hf.eq_iff] at he
  rcases he with ⟨rfl,rfl⟩
  rfl

private theorem parameters_injective {ge : G → List Bool} {fe : F → List Bool}
    (hg : Function.Injective ge) (hf : Function.Injective fe) : Function.Injective (parameters ge fe) := by
  rintro ⟨a,b,c,d,e⟩ ⟨f,g,h,i,j⟩ he
  simp only [parameters,pair_eq_iff,(cipher_injective hg).eq_iff,
    (schnorr_injective hg hf).eq_iff,
    (list_injective (BitRecordCodec.injective ballotNatBitCodec)).eq_iff,
    (list_injective (BitRecordCodec.injective ballotVoterBitCodec)).eq_iff,Prod.mk.injEq] at he
  rcases he with ⟨⟨rfl,rfl⟩,rfl,rfl,rfl⟩
  rfl

/-- All original fields can be recovered whenever the supplied leaf encoders
are injective; no bounded-shape assumption is needed for this fact. -/
theorem prefix_injective {ge : G → List Bool} {fe : F → List Bool}
    (hg : Function.Injective ge) (hf : Function.Injective fe) : Function.Injective (encodePrefix ge fe) := by
  rintro ⟨a,b,⟨c,d⟩,e⟩ ⟨f,g,⟨h,i⟩,j⟩ he
  simp only [encodePrefix,pair_eq_iff,(parameters_injective hg hf).eq_iff,
    (BitRecordCodec.injective ballotNatBitCodec).eq_iff,
    (BitRecordCodec.injective ballotDecisionBitCodec).eq_iff,(board_injective hg hf).eq_iff] at he
  rcases he with ⟨rfl,rfl,⟨rfl,rfl⟩,rfl⟩
  rfl

theorem result_injective {ge : G → List Bool} {fe : F → List Bool}
    (hg : Function.Injective ge) (hf : Function.Injective fe) : Function.Injective (encodeResult ge fe) := by
  rintro ⟨a,b,c,d,e,f,g,h⟩ ⟨i,j,k,l,m,n,o,p⟩ he
  simp only [encodeResult,pair_eq_iff,(prefix_injective hg hf).eq_iff,
    (ballot_injective hg hf).eq_iff,(BitRecordCodec.injective ballotDecisionBitCodec).eq_iff,
    (board_injective hg hf).eq_iff,(two_injective (cipher_injective hg)).eq_iff,
    (two_injective hg).eq_iff,(two_injective (schnorr_injective (cipher_injective hg) hf)).eq_iff,
    (two_injective (BitRecordCodec.injective ballotDecodedBitCodec)).eq_iff] at he
  rcases he with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  rfl

theorem scalar_bits_injective (q : Nat) [NeZero q] :
    Function.Injective (fun x : ZMod q => x.val.bits) := by
  intro x y h
  apply ZMod.val_injective
  simpa only [bitsValue_bits] using congrArg bitsValue h

namespace Controls
private def emptyPrefix (fp : Nat) : PublicPrefix Unit Unit :=
  ⟨⟨(),(),⟨(),()⟩,[0,1],[0,1,2]⟩,fp,(.accepted,.accepted),[]⟩

/-- Independent degenerate-leaf test: even when every leaf has the only possible
Unit value, the unbounded Nat fingerprint must remain visible in serialization. -/
theorem fingerprint_visible :
    encodePrefix (fun _ : Unit => []) (fun _ : Unit => []) (emptyPrefix 0) ≠
      encodePrefix (fun _ : Unit => []) (fun _ : Unit => []) (emptyPrefix 8) := by
  intro h
  have he := prefix_injective (fun _ _ _ => Subsingleton.elim _ _) (fun _ _ _ => Subsingleton.elim _ _) h
  have hn := congrArg PublicPrefix.fingerprint he
  change 0 = 8 at hn
  exact (by decide : (0 : Nat) ≠ 8) hn

theorem decoded_none_not_zero : ballotDecodedBitCodec.encode none ≠ ballotDecodedBitCodec.encode (some 0) := by
  decide
end Controls

#print axioms prime_prefix_eq
#print axioms prime_result_eq
#print axioms prefix_length_le
#print axioms result_length_le
#print axioms prefix_injective
#print axioms result_injective
end ExplainableCrypto.Helios.Computational.ElectionPublicEncoding
