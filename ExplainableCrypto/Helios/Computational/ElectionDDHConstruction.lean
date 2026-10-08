import ExplainableCrypto.Helios.Computational.NonzeroSimulationBridge
import ExplainableCrypto.Helios.Computational.HonestBallot
import ExplainableCrypto.Helios.Computational.Trustee

/-! Challenge ciphertexts for the historical abstention/candidate-0 swap.
The retained combined nonces permit share construction. These input laws do
not yet identify the complete election or prove computational secrecy. -/
namespace ExplainableCrypto.Helios.Computational.ElectionDDHConstruction
open OracleComp OracleComp.ProgramLogic OracleComp.ProgramLogic.Relational
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

abbrev Pair (G : Type) := (Fin 2 → Ciphertext G) × (Fin 2 → Ciphertext G)
abbrev Output (F G : Type) := Pair G × (Fin 2 → F)

/-- A and T come from the challenge. The reduction knows total and both zero
component nonces, but needs no discrete logarithm of A or T. -/
def paired (g pk A T : G) (total leftZero rightZero : F) (vote : Bool) : Output F G :=
  let c : Ciphertext G := (A,voteScalar (F := F) vote • g + T)
  ((![c,encryptWith g pk leftZero 0],
    ![encryptWith g pk total 1 - c,encryptWith g pk rightZero 0]),
    ![total,leftZero + rightZero])

/-- The actual honest vote vectors and the nonce information retained by the
reparameterization. Both second components encrypt zero. -/
def original (g pk : G) (alice leftZero bob rightZero : F) (vote : Bool) : Output F G :=
  ((![encryptWith g pk alice (voteScalar vote),encryptWith g pk leftZero 0],
    ![encryptWith g pk bob (voteScalar (!vote)),encryptWith g pk rightZero 0]),
    ![alice + bob,leftZero + rightZero])

/-- The reference ciphertext pair is exactly the pair in the existing
historical honest-ballot algorithm, for arbitrary proof coins and hash. -/
theorem original_honestBallots (hash : Hash F G) (g pk : G) (vote : Bool)
    (alice bob : HonestCoins F) :
    (original g pk (alice.nonce 0) (alice.nonce 1) (bob.nonce 0) (bob.nonce 1) vote).1 =
      ((honestBallot hash g pk vote alice).ciphertext,
       (honestBallot hash g pk (!vote) bob).ciphertext) := rfl

private theorem complement (vote : Bool) :
    1 - voteScalar (F := F) vote = voteScalar (!vote) := by
  cases vote <;> simp [voteScalar]

/-- Pointwise real-challenge identity; the combined nonce may be zero. -/
theorem paired_real (g pk : G) (alice leftZero bob rightZero : F) (vote : Bool) :
    paired g pk (alice • g) (alice • pk) (alice + bob) leftZero rightZero vote =
      original g pk alice leftZero bob rightZero vote := by
  have h : encryptWith g pk (alice + bob) 1 -
      encryptWith g pk alice (voteScalar vote) = encryptWith g pk bob (voteScalar (!vote)) := by
    apply sub_eq_iff_eq_add.mpr
    rw [encryptWith_add]
    congr 1
    · exact add_comm _ _
    · exact sub_eq_iff_eq_add.mp (complement (F := F) vote)
  simpa only [paired,original,encryptWith] using
    congrArg (fun c : Ciphertext G =>
      ((![encryptWith g pk alice (voteScalar vote),encryptWith g pk leftZero 0],
        ![c,encryptWith g pk rightZero 0]), ![alice + bob,leftZero + rightZero])) h

/-- Cancellation works even for a random, non-DH challenge. -/
theorem paired_totals (g pk A T : G) (total leftZero rightZero : F) (vote : Bool)
    (i : Fin 2) :
    let out := paired g pk A T total leftZero rightZero vote
    out.1.1 i + out.1.2 i = encryptWith g pk (out.2 i) (if i = 0 then 1 else 0) := by
  fin_cases i
  · simp [paired]
  · simpa [paired] using encryptWith_add g pk leftZero rightZero 0 0

/-- A share computed from the public key and actual extracted malicious nonce
is the trustee's share, with no secret supplied to the construction itself. -/
theorem tally_shares_eq (g A T : G) (secret total leftZero rightZero : F)
    (vote : Bool) (malicious : Fin 2 → Ciphertext G) (w : Fin 2 → BallotWitness F)
    (hw : ∀ i, (⟨g,secret • g,malicious i⟩ : BallotStatement G).Witnesses (w i))
    (i : Fin 2) :
    let out := paired g (secret • g) A T total leftZero rightZero vote
    (out.2 i + (w i).2) • (secret • g) =
      partialDecrypt secret (out.1.1 i + out.1.2 i + malicious i) := by
  dsimp only
  rw [paired_totals]
  have hm := hw i
  change malicious i = encryptWith g (secret • g) (w i).2 (voteScalar (w i).1) at hm
  rw [hm,encryptWith_add]
  simp [partialDecrypt,encryptWith,smul_smul,mul_comm]

/-- Shifting the unknown random mask absorbs the vote without changing the
ciphertexts or retained sums. -/
theorem paired_mask_shift (g pk A : G) (z total leftZero rightZero : F) (vote : Bool) :
    paired g pk A (z • g) total leftZero rightZero false =
      paired g pk A ((z - voteScalar (F := F) vote) • g) total leftZero rightZero vote := by
  have h : voteScalar (F := F) vote • g + (z - voteScalar (F := F) vote) • g = z • g := by
    rw [← add_smul]
    rw [add_sub_cancel]
  simp only [paired]
  rw [h]
  simp [voteScalar]

variable [Fintype F] [DecidableEq F] [SampleableType F]

omit [Fintype F] [DecidableEq F] in
/-- Equality of joint output laws, including the known nonce sums. Only the
full-field intermediate sampler is used in this exact identity. -/
theorem paired_ciphertexts_real_eq (g pk : G) (vote : Bool) :
    𝒮[do let alice ← uniformSample F; let leftZero ← uniformSample F
         let total ← uniformSample F; let rightZero ← uniformSample F
         pure (paired g pk (alice • g) (alice • pk) total leftZero rightZero vote)] =
    𝒮[do let alice ← uniformSample F; let leftZero ← uniformSample F
         let bob ← uniformSample F; let rightZero ← uniformSample F
         pure (original g pk alice leftZero bob rightZero vote)] := by
  apply evalSPMF_ext
  intro out
  symm
  apply probOutput_eq_of_relTriple_eqRel (x := out)
  refine relTriple_bind_uniformSample_bij (f := id) (fun alice => ?_) Function.bijective_id
  refine relTriple_bind_uniformSample_bij (f := id) (fun leftZero => ?_) Function.bijective_id
  refine relTriple_bind_uniformSample_bij (f := fun bob => alice + bob)
    (fun bob => ?_) (AddGroup.addLeft_bijective alice)
  refine relTriple_bind_uniformSample_bij (f := id) (fun rightZero => ?_) Function.bijective_id
  exact relTriple_pure_pure (paired_real g pk alice leftZero bob rightZero vote).symm

omit [Fintype F] [DecidableEq F] in
/-- Random-DDH ciphertext masking, for any fixed public key, first challenge
element and known nonces. This is an input law, not full election secrecy. -/
theorem paired_ciphertexts_random_eq (g pk A : G) (total leftZero rightZero : F) (vote : Bool) :
    𝒮[do let z ← uniformSample F
         pure (paired g pk A (z • g) total leftZero rightZero false)] =
    𝒮[do let z ← uniformSample F
         pure (paired g pk A (z • g) total leftZero rightZero vote)] := by
  apply evalSPMF_ext
  intro out
  apply probOutput_eq_of_relTriple_eqRel (x := out)
  refine relTriple_bind_uniformSample_bij (f := fun z : F => z - voteScalar (F := F) vote)
    (fun z => ?_) (sub_left_injective.bijective_of_finite)
  exact relTriple_pure_pure (paired_mask_shift g pk A z total leftZero rightZero vote)

/-- Four historical nonzero nonces incur a stated statistical loss. This does
not change the actual election sampler or condition the combined nonce. -/
theorem paired_ciphertexts_nonzero_distance_le (g pk : G) (vote : Bool) :
    tvDist
      (do let alice ← sampleNonzero F; let leftZero ← sampleNonzero F
          let bob ← sampleNonzero F; let rightZero ← sampleNonzero F
          pure (original g pk alice leftZero bob rightZero vote))
      (do let alice ← uniformSample F; let leftZero ← uniformSample F
          let total ← uniformSample F; let rightZero ← uniformSample F
          pure (paired g pk (alice • g) (alice • pk) total leftZero rightZero vote)) ≤
      4 * (Fintype.card F : ℝ)⁻¹ := by
  have he := paired_ciphertexts_real_eq (F := F) g pk vote
  unfold tvDist
  rw [he]
  change tvDist _ _ ≤ _
  let a := fun alice => do
    let leftZero ← sampleNonzero F; let bob ← sampleNonzero F; let rightZero ← sampleNonzero F
    pure (original g pk alice leftZero bob rightZero vote)
  let b := fun alice => do
    let leftZero ← uniformSample F; let bob ← uniformSample F; let rightZero ← uniformSample F
    pure (original g pk alice leftZero bob rightZero vote)
  change tvDist (sampleNonzero F >>= a) (uniformSample F >>= b) ≤ _
  calc
    _ ≤ tvDist (sampleNonzero F >>= a) (sampleNonzero F >>= b) +
        tvDist (sampleNonzero F >>= b) (uniformSample F >>= b) := tvDist_triangle _ _ _
    _ ≤ 3 * (Fintype.card F : ℝ)⁻¹ + (Fintype.card F : ℝ)⁻¹ :=
      add_le_add (tvDist_bind_left_le_const' _ _ _ _ (fun alice => three_nonzero_draws_tv_le _))
        ((tvDist_bind_right_le b _ _).trans sampleNonzero_uniform_tv_le)
    _ = _ := by ring

#print axioms paired_mask_shift
#print axioms paired_ciphertexts_random_eq
#print axioms original_honestBallots
#print axioms paired_real
#print axioms paired_totals
#print axioms tally_shares_eq
#print axioms paired_ciphertexts_real_eq
#print axioms paired_ciphertexts_nonzero_distance_le
end ExplainableCrypto.Helios.Computational.ElectionDDHConstruction
